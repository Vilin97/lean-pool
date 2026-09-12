/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz2
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1

/-!
# Hopf problem: homology theory · first hurewicz 3

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

private theorem SphereHomology.unitSphere_piTwo_subsingleton (n : ℕ) (x : UnitSphere (n + 3)) :
    Subsingleton (π_ 2 (UnitSphere (n + 3)) x) := by
  let := unitSphere_homology_subsingleton (n + 2) 2 (by decide) (by omega)
  exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton

private abbrev FirstHurewicz.AbelianPi1 (X : Type*) [TopologicalSpace X] (b : X) :=
  Additive (Abelianization (FundamentalGroup X b))

private def FirstHurewicz.loopQuotient {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk p

private def FirstHurewicz.loopClass {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    AbelianPi1 X b :=
  Additive.ofMul (Abelianization.of (loopQuotient p))

private theorem FirstHurewicz.loopClass_surjective {X : Type*} [TopologicalSpace X] {b : X} :
    Function.Surjective (loopClass (b := b)) := by
  intro a
  obtain ⟨g, hg⟩ := Quotient.exists_rep a.toMul
  change Abelianization.of g = a.toMul at hg
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g
  have hp' : loopQuotient p = g := hp
  refine ⟨p, ?_⟩
  rw [loopClass, hp', hg]
  rfl

private theorem FirstHurewicz.loopQuotient_trans {X : Type*} [TopologicalSpace X] {b : X}
    (p q : Path b b) : loopQuotient (p.trans q) = loopQuotient q * loopQuotient p :=
  rfl

private theorem
    FirstHurewicz.loopQuotient_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopQuotient p.symm = (loopQuotient p)⁻¹ :=
  rfl

private theorem FirstHurewicz.loopClass_homotopic {X : Type*} [TopologicalSpace X] {b : X}
    {p q : Path b b} (h : p.Homotopic q) : loopClass p = loopClass q :=
  congrArg (fun g : FundamentalGroup X b => Additive.ofMul (Abelianization.of g))
    (Path.Homotopic.Quotient.eq.mpr h)

private theorem
    FirstHurewicz.loopClass_trans {X : Type*} [TopologicalSpace X] {b : X} (p q : Path b b) :
    loopClass (p.trans q) = loopClass p + loopClass q := by
  rw [loopClass, loopQuotient_trans, map_mul, ofMul_mul, add_comm]
  rfl

@[simp]
private theorem
    FirstHurewicz.loopClass_symm {X : Type*} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopClass p.symm = -loopClass p := by
  rw [loopClass, loopQuotient_symm, map_inv, ofMul_inv]
  rfl

private def
    FirstHurewicz.basedLoop {X : Type*} [TopologicalSpace X] {b x y : X} (r : ∀ x : X, Path b x)
    (p : Path x y) : Path b b :=
  (r x).trans (p.trans (r y).symm)

private def FirstHurewicz.basedLoopQuotient {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) : FundamentalGroup X b :=
  Path.Homotopic.Quotient.mk (basedLoop r p)

private def FirstHurewicz.basedLoopClass {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) : AbelianPi1 X b :=
  loopClass (basedLoop r p)

private theorem FirstHurewicz.basedLoopClass_eq {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r p = Additive.ofMul (Abelianization.of (basedLoopQuotient r p)) :=
  rfl

private theorem FirstHurewicz.basedLoop_homotopic {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) {p q : Path x y} (h : p.Homotopic q) :
    (basedLoop r p).Homotopic (basedLoop r q) :=
  (Path.Homotopic.refl (r x)).hcomp (h.hcomp (Path.Homotopic.refl (r y).symm))

private theorem FirstHurewicz.basedLoopClass_homotopic {X : Type*} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) {p q : Path x y} (h : p.Homotopic q) :
    basedLoopClass r p = basedLoopClass r q :=
  loopClass_homotopic (basedLoop_homotopic r h)

private theorem FirstHurewicz.basedLoopQuotient_trans {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p : Path x y) (q : Path y z) :
    basedLoopQuotient r (p.trans q) = basedLoopQuotient r q * basedLoopQuotient r p := by
  simp only [basedLoopQuotient, basedLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc]
  rw [←
    Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (r y)).symm
      (Path.Homotopic.Quotient.mk (r y)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

private theorem FirstHurewicz.basedLoopClass_trans {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p : Path x y) (q : Path y z) :
    basedLoopClass r (p.trans q) = basedLoopClass r p + basedLoopClass r q := by
  rw [basedLoopClass_eq, basedLoopQuotient_trans, map_mul, ofMul_mul, add_comm, ←
    basedLoopClass_eq, ← basedLoopClass_eq]

@[simp]
private theorem FirstHurewicz.basedLoopClass_loop {X : Type*} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) : basedLoopClass r p = loopClass p := by
  rw [basedLoopClass, basedLoop, loopClass_trans, loopClass_trans, loopClass_symm]
  abel

private theorem FirstHurewicz.basedLoopClass_triangle {X : Type*} [TopologicalSpace X] {b x y z : X}
    (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₀₁ + basedLoopClass r p₁₂ = basedLoopClass r p₀₂ := by
  rw [← basedLoopClass_trans]
  exact basedLoopClass_homotopic r h

private theorem FirstHurewicz.basedLoopClass_triangle_boundary {X : Type*} [TopologicalSpace X]
    {b x y z : X} (r : ∀ x : X, Path b x) (p₀₁ : Path x y) (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₁₂ - basedLoopClass r p₀₂ + basedLoopClass r p₀₁ = 0 := by
  rw [← basedLoopClass_triangle r p₀₁ p₁₂ p₀₂ h]
  abel

private def FirstHurewicz.pathClass {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    Opchains X :=
  chainClass X (pathChain p)

private theorem FirstHurewicz.pathClass_homotopy {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : pathClass p = pathClass q :=
  (chainClass_eq_iff X _ _).mpr ⟨correctedHomotopyChain H, boundaryTwo_correctedHomotopyChain H⟩

private theorem FirstHurewicz.pathClass_homotopic {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (h : p.Homotopic q) : pathClass p = pathClass q := by
  obtain ⟨H⟩ := h
  exact pathClass_homotopy H

@[simp]
private theorem FirstHurewicz.pathClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathClass (Path.refl x) = 0 := by
  change chainClass X (pathChain (Path.refl x)) = 0
  rw [pathChain_refl, ← boundaryTwo_constantTriangleChain]
  exact chainClass_boundary X _

private theorem
    FirstHurewicz.pathClass_trans {X : Type} [TopologicalSpace X] {x y z : X} (p : Path x y)
    (q : Path y z) : pathClass (p.trans q) = pathClass p + pathClass q := by
  have h := chainClass_boundary X (concatChain p q)
  rw [boundaryTwo_concatChain, map_add, map_sub] at h
  change pathClass q - pathClass (p.trans q) + pathClass p = 0 at h
  apply sub_eq_zero.mp
  calc
    pathClass (p.trans q) - (pathClass p + pathClass q) =
        -(pathClass q - pathClass (p.trans q) + pathClass p) := by abel
    _ = 0 := by rw [h, neg_zero]

@[simp]
private theorem
    FirstHurewicz.pathClass_symm {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) :
    pathClass p.symm = -pathClass p := by
  have h := pathClass_homotopic (Path.Homotopic.trans_symm p)
  rw [pathClass_trans, pathClass_refl] at h
  exact eq_neg_of_add_eq_zero_right h

@[simp]
private theorem
    FirstHurewicz.pathClass_cast {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y)
    {x' y' : X} (hx : x' = x) (hy : y' = y) : pathClass (p.cast hx hy) = pathClass p :=
  rfl

/-- The singular one-cycle represented by a based loop. -/
public
def
    FirstHurewicz.loopCycle {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) : Cycles1 X :=
  mkCycle1 X (pathChain p) (boundaryOne_loop p)

@[simp]
private theorem FirstHurewicz.loopCycle_val {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    (loopCycle p).1 = pathChain p :=
  rfl

/-- The first singular-homology class represented by a based loop. -/
public
def FirstHurewicz.loopHomologyClass {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    SingularH1 X :=
  cycleClass X (loopCycle p)

@[simp]
private theorem FirstHurewicz.homologyToChainClass_loopHomologyClass {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x) : homologyToChainClass X (loopHomologyClass p) = pathClass p := by
  rw [loopHomologyClass, homologyToChainClass_cycleClass]
  rfl

private theorem FirstHurewicz.loopHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : Path x x} (h : p.Homotopic q) : loopHomologyClass p = loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass]
  exact pathClass_homotopic h

@[simp]
private theorem FirstHurewicz.loopHomologyClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    loopHomologyClass (Path.refl x) = 0 := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, pathClass_refl, map_zero]

private theorem FirstHurewicz.loopHomologyClass_trans {X : Type} [TopologicalSpace X] {x : X}
    (p q : Path x x) :
    loopHomologyClass (p.trans q) = loopHomologyClass p + loopHomologyClass q := by
  apply homologyToChainClass_injective X
  rw [homologyToChainClass_loopHomologyClass, map_add, homologyToChainClass_loopHomologyClass,
    homologyToChainClass_loopHomologyClass, pathClass_trans]

private def FirstHurewicz.hurewiczFunction {X : Type} [TopologicalSpace X] (b : X) :
    FundamentalGroup X b → SingularH1 X :=
  Quotient.lift (fun p : Path b b => loopHomologyClass p)
    (fun _ _ h => loopHomologyClass_homotopic h)

private def FirstHurewicz.hurewiczPi1 {X : Type} [TopologicalSpace X] (b : X) :
    FundamentalGroup X b →* Multiplicative (SingularH1 X)
    where
  toFun g := Multiplicative.ofAdd (hurewiczFunction b g)
  map_one' := congrArg Multiplicative.ofAdd (loopHomologyClass_refl b)
  map_mul' g
    h := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective h
    change
      Multiplicative.ofAdd (loopHomologyClass (q.trans p)) =
        Multiplicative.ofAdd (loopHomologyClass p + loopHomologyClass q)
    rw [loopHomologyClass_trans, add_comm]

private def FirstHurewicz.hurewiczMap {X : Type} [TopologicalSpace X] (b : X) :
    AbelianPi1 X b →ₗ[ℤ] SingularH1 X
    where
  toFun := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft
  map_add' := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft.map_add
  map_smul' n
    a := by
    simpa using map_intCast_smul (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft ℤ ℤ n a

@[simp]
private theorem FirstHurewicz.hurewiczMap_loopClass {X : Type} [TopologicalSpace X] (b : X)
    (p : Path b b) : hurewiczMap b (loopClass p) = loopHomologyClass p :=
  rfl

private theorem
    FirstHurewicz.homologyToChainClass_hurewiczMap_loopClass {X : Type} [TopologicalSpace X]
    (b : X) (p : Path b b) : homologyToChainClass X (hurewiczMap b (loopClass p)) = pathClass p :=
  by rw [hurewiczMap_loopClass, homologyToChainClass_loopHomologyClass]

private theorem
    FirstHurewicz.hurewiczMap_basedLoopClass {X : Type} [TopologicalSpace X] {x y : X} (b : X)
    (r : ∀ a : X, Path b a) (p : Path x y) :
    homologyToChainClass X (hurewiczMap b (basedLoopClass r p)) =
      pathClass (r x) + pathClass p - pathClass (r y) := by
  change homologyToChainClass X (hurewiczMap b (loopClass (basedLoop r p))) = _
  rw [homologyToChainClass_hurewiczMap_loopClass]
  change pathClass ((r x).trans (p.trans (r y).symm)) = _
  rw [pathClass_trans, pathClass_trans, pathClass_symm]
  abel

private theorem FirstHurewicz.basedLoopClass_cast {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) {x' y' : X} (hx : x' = x) (hy : y' = y) :
    basedLoopClass r (p.cast hx hy) = basedLoopClass r p := by
  cases hx
  cases hy
  rfl

private theorem FirstHurewicz.simplexPath_pathSimplex_cast {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) :
    simplexPath (pathSimplex p) = p.cast (pathSimplex_vertex_zero p) (pathSimplex_vertex_one p) :=
  by
  apply Path.ext
  funext t
  change p (stdSimplexHomeomorphUnitInterval (stdSimplexHomeomorphUnitInterval.symm t)) = p t
  rw [Homeomorph.apply_symm_apply]

@[simp]
private theorem FirstHurewicz.basedLoopClass_simplexPath_pathSimplex {X : Type} [TopologicalSpace X]
    {b x y : X} (r : ∀ x : X, Path b x) (p : Path x y) :
    basedLoopClass r (simplexPath (pathSimplex p)) = basedLoopClass r p := by
  rw [simplexPath_pathSimplex_cast, basedLoopClass_cast]

private theorem
    FirstHurewicz.basedLoopClass_triangleFacePath {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) (i : Fin 3) :
    basedLoopClass r (triangleFacePath σ i) =
      basedLoopClass r (simplexPath (σ.comp (simplexFace 1 i))) :=
  basedLoopClass_cast r (simplexPath (σ.comp (simplexFace 1 i))) _ _

private def FirstHurewicz.edgeLoopCochain {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : Chains X 1 →ₗ[ℤ] AbelianPi1 X b :=
  chainLift X 1 (fun σ => basedLoopClass r (simplexPath σ))

@[simp]
private theorem FirstHurewicz.edgeLoopCochain_simplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 1) :
    edgeLoopCochain r (simplexChain X 1 σ) = basedLoopClass r (simplexPath σ) :=
  chainLift_simplex X 1 (fun σ => basedLoopClass r (simplexPath σ)) σ

private theorem
    FirstHurewicz.edgeLoopCochain_pathSimplex {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = basedLoopClass r p := by
  rw [edgeLoopCochain_simplex, basedLoopClass_simplexPath_pathSimplex]

private theorem FirstHurewicz.edgeLoopCochain_loopSimplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) :
    edgeLoopCochain r (simplexChain X 1 (pathSimplex p)) = loopClass p := by
  rw [edgeLoopCochain_pathSimplex, basedLoopClass_loop]

private theorem
    FirstHurewicz.edgeLoopCochain_boundaryTwo_simplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (σ : SingularSimplex X 2) :
    edgeLoopCochain r (boundaryTwo X (simplexChain X 2 σ)) = 0 := by
  simp only [boundaryTwo_simplex, map_add, map_sub, edgeLoopCochain_simplex]
  change
    basedLoopClass r (simplexPath (σ.comp (simplexFace 1 0))) -
          basedLoopClass r (simplexPath (σ.comp (simplexFace 1 1))) +
        basedLoopClass r (simplexPath (σ.comp (simplexFace 1 2))) =
      0
  have he :=
    congrArg₂ (fun a c : AbelianPi1 X b => a + c)
      (congrArg₂ (fun a c : AbelianPi1 X b => a - c) (basedLoopClass_triangleFacePath r σ 0)
        (basedLoopClass_triangleFacePath r σ 1))
      (basedLoopClass_triangleFacePath r σ 2)
  exact
    he.symm.trans
      (basedLoopClass_triangle_boundary r (triangleEdge01 σ) (triangleEdge12 σ) (triangleEdge02 σ)
        (triangleEdges_homotopic σ))

private theorem
    FirstHurewicz.edgeLoopCochain_comp_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : (edgeLoopCochain r).comp (boundaryTwo X) = 0 := by
  apply chainMap_ext X 2
  intro σ
  exact edgeLoopCochain_boundaryTwo_simplex r σ

private theorem FirstHurewicz.edgeLoopCochain_boundaryTwo {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Chains X 2) : edgeLoopCochain r (boundaryTwo X c) = 0 :=
  LinearMap.congr_fun (edgeLoopCochain_comp_boundaryTwo r) c

private def FirstHurewicz.inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : SingularH1 X →ₗ[ℤ] AbelianPi1 X b :=
  homologyDescOfChain X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r)

@[simp]
private theorem FirstHurewicz.inverseHurewiczMap_cycleClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    inverseHurewiczMap r (cycleClass X c) = edgeLoopCochain r c.1 :=
  homologyDescOfChain_cycleClass X (edgeLoopCochain r) (edgeLoopCochain_boundaryTwo r) c

private def
    FirstHurewicz.basePathChain {X : Type} [TopologicalSpace X] {b : X} (r : ∀ x : X, Path b x) :
    Chains X 0 →ₗ[ℤ] Chains X 1 :=
  chainLift X 0 (fun σ => pathChain (r (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))))

@[simp]
private theorem FirstHurewicz.basePathChain_pointChain {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (x : X) : basePathChain r (pointChain x) = pathChain (r x) :=
  chainLift_simplex X 0 _ (ContinuousMap.const (Simplex 0) x)

private theorem FirstHurewicz.edgeClosure_pathChain {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ x : X, Path b x) (p : Path x y) :
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r (pathChain p))) =
      chainClass X (pathChain p) - chainClass X (basePathChain r (boundaryOne X (pathChain p))) :=
  by
  have he : edgeLoopCochain r (pathChain p) = basedLoopClass r p :=
    edgeLoopCochain_pathSimplex r p
  rw [he, hurewiczMap_basedLoopClass, boundaryOne_pathChain, map_sub, basePathChain_pointChain,
    basePathChain_pointChain, map_sub]
  change
    pathClass (r x) + pathClass p - pathClass (r y) =
      pathClass p - (pathClass (r y) - pathClass (r x))
  abel

private theorem FirstHurewicz.edgeClosure_chain_identity {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) :
    (homologyToChainClass X).comp ((hurewiczMap b).comp (edgeLoopCochain r)) =
      chainClass X - (chainClass X).comp ((basePathChain r).comp (boundaryOne X)) := by
  apply chainMap_ext X 1
  intro σ
  have h := edgeClosure_pathChain r (simplexPath σ)
  simpa only [pathChain, pathSimplex_simplexPath, LinearMap.comp_apply, LinearMap.sub_apply] using
    h

private theorem FirstHurewicz.edgeClosure_cycle {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (c : Cycles1 X) :
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) = chainClass X c.1 := by
  have h := LinearMap.congr_fun (edgeClosure_chain_identity r) c.1
  change
    homologyToChainClass X (hurewiczMap b (edgeLoopCochain r c.1)) =
      chainClass X c.1 - chainClass X (basePathChain r (boundaryOne X c.1)) at h
  simpa only [cycles1_boundary, map_zero, sub_zero] using h

@[simp]
private theorem
    FirstHurewicz.inverseHurewiczMap_loopHomologyClass {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (p : Path b b) :
    inverseHurewiczMap r (loopHomologyClass p) = loopClass p := by
  rw [loopHomologyClass, inverseHurewiczMap_cycleClass, loopCycle_val]
  exact edgeLoopCochain_loopSimplex r p

private theorem FirstHurewicz.inverseHurewiczMap_hurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : AbelianPi1 X b) : inverseHurewiczMap r (hurewiczMap b a) = a := by
  obtain ⟨p, rfl⟩ := loopClass_surjective a
  rw [hurewiczMap_loopClass, inverseHurewiczMap_loopHomologyClass]

private theorem FirstHurewicz.hurewiczMap_inverseHurewiczMap {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) (a : SingularH1 X) : hurewiczMap b (inverseHurewiczMap r a) = a := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective X a
  apply homologyToChainClass_injective X
  rw [inverseHurewiczMap_cycleClass, homologyToChainClass_cycleClass]
  exact edgeClosure_cycle r c

private def FirstHurewicz.firstHurewiczEquivOfPaths {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ x : X, Path b x) : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X
    where
  toLinearMap := hurewiczMap b
  invFun := inverseHurewiczMap r
  left_inv := inverseHurewiczMap_hurewiczMap r
  right_inv := hurewiczMap_inverseHurewiczMap r

private def FirstHurewicz.firstHurewiczEquiv {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : AbelianPi1 X b ≃ₗ[ℤ] SingularH1 X :=
  firstHurewiczEquivOfPaths (PathConnectedSpace.somePath b)

@[simp]
private theorem FirstHurewicz.firstHurewiczEquiv_loopClass {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] (p : Path b b) :
    firstHurewiczEquiv b (loopClass p) = loopHomologyClass p :=
  hurewiczMap_loopClass b p

private theorem FirstHurewicz.loopHomologyClass_surjective {X : Type} [TopologicalSpace X] (b : X)
    [PathConnectedSpace X] : Function.Surjective (loopHomologyClass (x := b)) := by
  intro a
  obtain ⟨c, hc⟩ := (firstHurewiczEquiv b).surjective a
  obtain ⟨p, hp⟩ := loopClass_surjective c
  refine ⟨p, ?_⟩
  rw [← firstHurewiczEquiv_loopClass, hp, hc]

private def FirstHurewicz.abelianPi1EquivOfPi1 {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] (e : FundamentalGroup X b ≃* Multiplicative A) :
    AbelianPi1 X b ≃ₗ[ℤ] A :=
  (e.abelianizationCongr.trans
      (Abelianization.equivOfComm (H := Multiplicative A)).symm).toAdditiveLeft.toIntLinearEquiv

@[simp]
private theorem
    FirstHurewicz.abelianPi1EquivOfPi1_of {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] (e : FundamentalGroup X b ≃* Multiplicative A)
    (g : FundamentalGroup X b) :
    abelianPi1EquivOfPi1 b e (Additive.ofMul (Abelianization.of g)) = (e g).toAdd :=
  rfl

private def FirstHurewicz.singularH1EquivOfPi1 {X : Type} [TopologicalSpace X] (b : X) {A : Type*}
    [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) : SingularH1 X ≃ₗ[ℤ] A :=
  (firstHurewiczEquiv b).symm.trans (abelianPi1EquivOfPi1 b e)

@[simp]
private theorem FirstHurewicz.singularH1EquivOfPi1_hurewiczFunction {X : Type} [TopologicalSpace X]
    (b : X) {A : Type*} [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) (g : FundamentalGroup X b) :
    singularH1EquivOfPi1 b e (hurewiczFunction b g) = (e g).toAdd := by
  change
    abelianPi1EquivOfPi1 b e
        ((firstHurewiczEquiv b).symm
          (firstHurewiczEquiv b (Additive.ofMul (Abelianization.of g)))) =
      _
  rw [LinearEquiv.symm_apply_apply, abelianPi1EquivOfPi1_of]

@[simp]
private theorem FirstHurewicz.singularH1EquivOfPi1_loopHomologyClass {X : Type} [TopologicalSpace X]
    (b : X) {A : Type*} [AddCommGroup A] [Module ℤ A] [PathConnectedSpace X]
    (e : FundamentalGroup X b ≃* Multiplicative A) (p : Path b b) :
    singularH1EquivOfPi1 b e (loopHomologyClass p) = (e (loopQuotient p)).toAdd :=
  singularH1EquivOfPi1_hurewiczFunction b e (loopQuotient p)

private theorem FirstHurewicz.pathSimplex_map {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (f : C(X, Y)) (p : Path x y) :
    pathSimplex (p.map f.continuous) = f.comp (pathSimplex p) :=
  rfl

@[simp]
private theorem FirstHurewicz.inducedChain_pathChain {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {x y : X} (f : C(X, Y)) (p : Path x y) :
    inducedChain f 1 (pathChain p) = pathChain (p.map f.continuous) := by
  simp only [pathChain, inducedChain_simplex, pathSimplex_map]

@[simp]
private theorem FirstHurewicz.inducedCycles_loopCycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedCycles f (loopCycle p) = loopCycle (p.map f.continuous) := by
  apply Subtype.ext
  rw [inducedCycles_val, loopCycle_val, loopCycle_val, inducedChain_pathChain]

@[simp]
private theorem FirstHurewicz.inducedHomology_loopHomologyClass {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (b : X) (p : Path b b) :
    inducedHomology f (loopHomologyClass p) = loopHomologyClass (p.map f.continuous) := by
  rw [loopHomologyClass, inducedHomology_cycleClass, inducedCycles_loopCycle]
  rfl

private def
    SingularMayerVietoris.coverRestriction {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) : C(A, B) :=
  ⟨fun x => ⟨f x, hf x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

private def SingularMayerVietoris.intersectionRestriction {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : C((U ∩ V : Set X), (U' ∩ V' : Set Y)) :=
  coverRestriction f (U ∩ V) (U' ∩ V') (fun _ hx => ⟨hfU hx.1, hfV hx.2⟩)

private theorem SingularMayerVietoris.coverRestriction_ambient {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B) :
    FirstHurewicz.singularChainMap (coverRestriction f A B hf) ≫
        FirstHurewicz.singularChainMap (subtypeInclusion B) =
      FirstHurewicz.singularChainMap (subtypeInclusion A) ≫ FirstHurewicz.singularChainMap f := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  have h₁ :=
    F.map_comp (TopCat.ofHom (coverRestriction f A B hf)) (TopCat.ofHom (subtypeInclusion B))
  have h₂ := F.map_comp (TopCat.ofHom (subtypeInclusion A)) (TopCat.ofHom f)
  exact h₁.symm.trans h₂

private theorem
    SingularMayerVietoris.coverRestriction_intersection_left {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    intersectionToLeft U V ≫ FirstHurewicz.singularChainMap (coverRestriction f U U' hfU) =
      FirstHurewicz.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        intersectionToLeft U' V' := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  have h₁ :=
    F.map_comp (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.ofHom (coverRestriction f U U' hfU))
  have h₂ :=
    F.map_comp (TopCat.ofHom (intersectionRestriction f U V U' V' hfU hfV))
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U' ∩ V' ⊆ U')))
  exact h₁.symm.trans h₂

private theorem SingularMayerVietoris.coverRestriction_intersection_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') :
    intersectionToRight U V ≫ FirstHurewicz.singularChainMap (coverRestriction f V V' hfV) =
      FirstHurewicz.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        intersectionToRight U' V' := by
  let F := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  have h₁ :=
    F.map_comp (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)))
      (TopCat.ofHom (coverRestriction f V V' hfV))
  have h₂ :=
    F.map_comp (TopCat.ofHom (intersectionRestriction f U V U' V' hfU hfV))
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U' ∩ V' ⊆ V')))
  exact h₁.symm.trans h₂

private theorem
    SingularMayerVietoris.inducedChain_mem_small_of_mapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (n : ℕ) (c : FirstHurewicz.Chains X n)
    (hc : c ∈ smallChainSubmodule U V n) :
    FirstHurewicz.inducedChain f n c ∈ smallChainSubmodule U' V' n := by
  have hle :
    smallChainSubmodule U V n ≤
      (smallChainSubmodule U' V' n).comap (FirstHurewicz.inducedChain f n) := by
    rw [smallChainSubmodule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change
      FirstHurewicz.inducedChain f n (FirstHurewicz.simplexChain X n σ) ∈
        smallChainSubmodule U' V' n
    rw [FirstHurewicz.inducedChain_simplex]
    apply simplexChain_mem_small
    rcases hσ with hσ | hσ
    · left
      rintro _ ⟨s, rfl⟩
      exact hfU (hσ ⟨s, rfl⟩)
    · right
      rintro _ ⟨s, rfl⟩
      exact hfV (hσ ⟨s, rfl⟩)
  exact hle hc

private def
    SingularMayerVietoris.smallMapOfMapsTo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : smallComplex U V ⟶ smallComplex U' V' :=
  liftToSmall U' V' (smallInclusion U V ≫ FirstHurewicz.singularChainMap f)
    (fun n c => inducedChain_mem_small_of_mapsTo f U V U' V' hfU hfV n c.1 c.2)

@[simp]
private theorem SingularMayerVietoris.smallMapOfMapsTo_inclusion {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V' =
      smallInclusion U V ≫ FirstHurewicz.singularChainMap f :=
  liftToSmall_inclusion U' V' _ _

private theorem SingularMayerVietoris.toSmallLeft_smallMapOfMapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    toSmallLeft U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV =
      FirstHurewicz.singularChainMap (coverRestriction f U U' hfU) ≫ toSmallLeft U' V' := by
  apply (CategoryTheory.cancel_mono (smallInclusion U' V')).mp
  calc
    (toSmallLeft U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV) ≫ smallInclusion U' V' =
        toSmallLeft U V ≫ (smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V') :=
      CategoryTheory.Category.assoc _ _ _
    _ = toSmallLeft U V ≫ (smallInclusion U V ≫ FirstHurewicz.singularChainMap f) :=
      (congrArg (toSmallLeft U V ≫ ·) (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV))
    _ = (toSmallLeft U V ≫ smallInclusion U V) ≫ FirstHurewicz.singularChainMap f :=
      (CategoryTheory.Category.assoc _ _ _).symm
    _ = FirstHurewicz.singularChainMap (subtypeInclusion U) ≫ FirstHurewicz.singularChainMap f :=
      (congrArg (· ≫ FirstHurewicz.singularChainMap f) (toSmallLeft_inclusion U V))
    _ =
        FirstHurewicz.singularChainMap (coverRestriction f U U' hfU) ≫
          FirstHurewicz.singularChainMap (subtypeInclusion U') :=
      (coverRestriction_ambient f U U' hfU).symm
    _ =
        FirstHurewicz.singularChainMap (coverRestriction f U U' hfU) ≫
          (toSmallLeft U' V' ≫ smallInclusion U' V') :=
      (congrArg (FirstHurewicz.singularChainMap (coverRestriction f U U' hfU) ≫ ·)
        (toSmallLeft_inclusion U' V').symm)
    _ =
        (FirstHurewicz.singularChainMap (coverRestriction f U U' hfU) ≫ toSmallLeft U' V') ≫
          smallInclusion U' V' :=
      (CategoryTheory.Category.assoc _ _ _).symm

private theorem
    SingularMayerVietoris.toSmallRight_smallMapOfMapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    toSmallRight U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV =
      FirstHurewicz.singularChainMap (coverRestriction f V V' hfV) ≫ toSmallRight U' V' := by
  apply (CategoryTheory.cancel_mono (smallInclusion U' V')).mp
  calc
    (toSmallRight U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV) ≫ smallInclusion U' V' =
        toSmallRight U V ≫ (smallMapOfMapsTo f U V U' V' hfU hfV ≫ smallInclusion U' V') :=
      CategoryTheory.Category.assoc _ _ _
    _ = toSmallRight U V ≫ (smallInclusion U V ≫ FirstHurewicz.singularChainMap f) :=
      (congrArg (toSmallRight U V ≫ ·) (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV))
    _ = (toSmallRight U V ≫ smallInclusion U V) ≫ FirstHurewicz.singularChainMap f :=
      (CategoryTheory.Category.assoc _ _ _).symm
    _ = FirstHurewicz.singularChainMap (subtypeInclusion V) ≫ FirstHurewicz.singularChainMap f :=
      (congrArg (· ≫ FirstHurewicz.singularChainMap f) (toSmallRight_inclusion U V))
    _ =
        FirstHurewicz.singularChainMap (coverRestriction f V V' hfV) ≫
          FirstHurewicz.singularChainMap (subtypeInclusion V') :=
      (coverRestriction_ambient f V V' hfV).symm
    _ =
        FirstHurewicz.singularChainMap (coverRestriction f V V' hfV) ≫
          (toSmallRight U' V' ≫ smallInclusion U' V') :=
      (congrArg (FirstHurewicz.singularChainMap (coverRestriction f V V' hfV) ≫ ·)
        (toSmallRight_inclusion U' V').symm)
    _ =
        (FirstHurewicz.singularChainMap (coverRestriction f V V' hfV) ≫ toSmallRight U' V') ≫
          smallInclusion U' V' :=
      (CategoryTheory.Category.assoc _ _ _).symm

private def
    SingularMayerVietoris.coverMiddleMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : middleComplex U V ⟶ middleComplex U' V' :=
  CategoryTheory.Limits.biprod.map (FirstHurewicz.singularChainMap (coverRestriction f U U' hfU))
    (FirstHurewicz.singularChainMap (coverRestriction f V V' hfV))

private theorem
    SingularMayerVietoris.intersectionRestriction_leftMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    FirstHurewicz.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫ leftMap U' V' =
      leftMap U V ≫ coverMiddleMap f U V U' V' hfU hfV := by
  change
    FirstHurewicz.singularChainMap (intersectionRestriction f U V U' V' hfU hfV) ≫
        CategoryTheory.Limits.biprod.lift (intersectionToLeft U' V')
          (-(intersectionToRight U' V')) =
      CategoryTheory.Limits.biprod.lift (intersectionToLeft U V) (-(intersectionToRight U V)) ≫
        CategoryTheory.Limits.biprod.map
          (FirstHurewicz.singularChainMap (coverRestriction f U U' hfU))
          (FirstHurewicz.singularChainMap (coverRestriction f V V' hfV))
  apply CategoryTheory.Limits.biprod.hom_ext
  · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_fst,
      CategoryTheory.Limits.biprod.map_fst, CategoryTheory.Limits.biprod.lift_fst_assoc]
    exact (coverRestriction_intersection_left f U V U' V' hfU hfV).symm
  · simp only [CategoryTheory.Category.assoc, CategoryTheory.Limits.biprod.lift_snd,
      CategoryTheory.Limits.biprod.map_snd, CategoryTheory.Limits.biprod.lift_snd_assoc,
      CategoryTheory.Preadditive.comp_neg, CategoryTheory.Preadditive.neg_comp]
    exact congrArg Neg.neg (coverRestriction_intersection_right f U V U' V' hfU hfV).symm

private theorem SingularMayerVietoris.coverMiddleMap_rightMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') :
    coverMiddleMap f U V U' V' hfU hfV ≫ rightMap U' V' =
      rightMap U V ≫ smallMapOfMapsTo f U V U' V' hfU hfV := by
  change
    CategoryTheory.Limits.biprod.map
          (FirstHurewicz.singularChainMap (coverRestriction f U U' hfU))
          (FirstHurewicz.singularChainMap (coverRestriction f V V' hfV)) ≫
        CategoryTheory.Limits.biprod.desc (toSmallLeft U' V') (toSmallRight U' V') =
      CategoryTheory.Limits.biprod.desc (toSmallLeft U V) (toSmallRight U V) ≫
        smallMapOfMapsTo f U V U' V' hfU hfV
  apply CategoryTheory.Limits.biprod.hom_ext'
  · simp only [CategoryTheory.Limits.biprod.inl_map_assoc,
      CategoryTheory.Limits.biprod.inl_desc_assoc, CategoryTheory.Limits.biprod.inl_desc]
    exact (toSmallLeft_smallMapOfMapsTo f U V U' V' hfU hfV).symm
  · simp only [CategoryTheory.Limits.biprod.inr_map_assoc,
      CategoryTheory.Limits.biprod.inr_desc_assoc, CategoryTheory.Limits.biprod.inr_desc]
    exact (toSmallRight_smallMapOfMapsTo f U V U' V' hfU hfV).symm

private def SingularMayerVietoris.chainSequenceMapOfMapsTo {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') : chainSequence U V ⟶ chainSequence U' V'
    where
  τ₁ := FirstHurewicz.singularChainMap (intersectionRestriction f U V U' V' hfU hfV)
  τ₂ := coverMiddleMap f U V U' V' hfU hfV
  τ₃ := smallMapOfMapsTo f U V U' V' hfU hfV
  comm₁₂ := intersectionRestriction_leftMap f U V U' V' hfU hfV
  comm₂₃ := coverMiddleMap_rightMap f U V U' V' hfU hfV

private theorem SingularMayerVietoris.smallHomologyComparison_naturality_of_comm {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (g : smallComplex U V ⟶ smallComplex U' V')
    (hg : g ≫ smallInclusion U' V' = smallInclusion U V ≫ FirstHurewicz.singularChainMap f)
    (n : ℕ) (a : SmallHomology U V n) :
    smallHomologyComparison U' V' n (homologyLinearMap g n a) =
      singularHomologyMap f n (smallHomologyComparison U V n a) := by
  have h := congrArg (fun q => homologyLinearMap q n) hg
  rw [homologyLinearMap_comp, homologyLinearMap_comp] at h
  exact LinearMap.congr_fun h a

private theorem SingularMayerVietoris.connectingHomomorphism_naturality_of_sequenceMap {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (hU' : IsOpen U')
    (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ) (φ : chainSequence U V ⟶ chainSequence U' V')
    (hφ : φ.τ₃ ≫ smallInclusion U' V' = smallInclusion U V ≫ FirstHurewicz.singularChainMap f)
    (n : ℕ) :
    (homologyLinearMap φ.τ₁ n).comp (connectingHomomorphism U V hU hV hcover n) =
      (connectingHomomorphism U' V' hU' hV' hcover' n).comp (singularHomologyMap f (n + 1)) := by
  apply LinearMap.ext
  intro a
  obtain ⟨b, hb⟩ := (smallHomologyEquiv U V hU hV hcover (n + 1)).surjective a
  have hb' : smallHomologyComparison U V (n + 1) b = a := hb
  change
    homologyLinearMap φ.τ₁ n (connectingHomomorphism U V hU hV hcover n a) =
      connectingHomomorphism U' V' hU' hV' hcover' n (singularHomologyMap f (n + 1) a)
  rw [← hb', connectingHomomorphism_comparison]
  have hδ :
    homologyLinearMap φ.τ₁ n (smallConnectingMap U V n b) =
      smallConnectingMap U' V' n (homologyLinearMap φ.τ₃ (n + 1) b) :=
    LinearMap.congr_fun
      (connectingMap_naturality (chainSequence_shortExact U V) φ (chainSequence_shortExact U' V')
        n)
      b
  have hc :=
    (connectingHomomorphism_comparison U' V' hU' hV' hcover' n
        (homologyLinearMap φ.τ₃ (n + 1) b)).symm
  have hn :=
    congrArg (connectingHomomorphism U' V' hU' hV' hcover' n)
      (smallHomologyComparison_naturality_of_comm f U V U' V' φ.τ₃ hφ (n + 1) b)
  exact hδ.trans (hc.trans hn)

private theorem
    SingularMayerVietoris.connectingHomomorphism_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (hfU : Set.MapsTo f U U')
    (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ) (n : ℕ) :
    (singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n).comp
        (connectingHomomorphism U V hU hV hcover n) =
      (connectingHomomorphism U' V' hU' hV' hcover' n).comp (singularHomologyMap f (n + 1)) :=
  connectingHomomorphism_naturality_of_sequenceMap f U V U' V' hU hV hcover hU' hV' hcover'
    (chainSequenceMapOfMapsTo f U V U' V' hfU hfV)
    (smallMapOfMapsTo_inclusion f U V U' V' hfU hfV) n

private theorem SingularMayerVietoris.connectingHomomorphism_naturality_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)
    (n : ℕ) (a : SingularHomology X (n + 1)) :
    singularHomologyMap (intersectionRestriction f U V U' V' hfU hfV) n
        (connectingHomomorphism U V hU hV hcover n a) =
      connectingHomomorphism U' V' hU' hV' hcover' n (singularHomologyMap f (n + 1) a) :=
  LinearMap.congr_fun
    (connectingHomomorphism_naturality f U V U' V' hfU hfV hU hV hcover hU' hV' hcover' n) a

end Mathoverflow1973

end
