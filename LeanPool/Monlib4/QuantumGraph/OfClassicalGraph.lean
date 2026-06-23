/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import LeanPool.Monlib4.QuantumGraph.Basic
import LeanPool.Monlib4.QuantumGraph.Example
import LeanPool.Monlib4.QuantumGraph.Grad

/-!
# LeanPool.Monlib4.QuantumGraph.OfClassicalGraph

Imported Lean Pool material for `LeanPool.Monlib4.QuantumGraph.OfClassicalGraph`.
-/

noncomputable instance {n : Type*} :
  starAlgebra (PiQ (fun _ : n => ℂ)) :=
piStarAlgebra
noncomputable instance {n : Type*} [Fintype n] :
  QuantumSet (PiQ (fun _ : n => ℂ)) := by
  letI : Fact (∀ i : n, (QuantumSet.k (A := ℂ)) = 0) := Fact.mk (fun _ => rfl)
  infer_instance

open scoped InnerProductSpace

theorem EuclideanSpace.comul_eq {n : Type*} [Fintype n] [DecidableEq n] (x : PiQ (fun _ : n => ℂ))
  :
  let e : ∀ _ : n, (PiQ (fun _ : n => ℂ)) := fun i => PiLp.single 2 i (1 : ℂ)
  (Coalgebra.comul : PiQ (fun _ : n => ℂ) →ₗ[ℂ] _) x
    = ∑ i, x i • (e i ⊗ₜ[ℂ] e i) := by
  intro e
  have : ∀ y i, ⟪e i, y⟫_ℂ = y i := fun y i => by
    simpa [e] using (EuclideanSpace.basisFun_inner (𝕜 := ℂ) (ι := n) y i)
  rw [TensorProduct.inner_ext_iff']
  intro a b
  simp only [TensorProduct.inner_tmul, Coalgebra.comul, LinearMap.adjoint_inner_left,
    LinearMap.mul'_apply, sum_inner, inner_smul_left, this]
  simp only [PiLp.inner_apply, RCLike.inner_apply']
  rfl

open scoped Matrix
/-- a finite simple graph is a quantum graph -/
theorem SimpleGraph.toQuantumGraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  QuantumGraph _ (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G)) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  let e : ∀ _ : V, EuclideanSpace ℂ V := fun i => PiLp.single 2 i (1 : ℂ)
  have he : ∀ i, e i = PiLp.single 2 i (1 : ℂ) := fun _ => rfl
  have : ∀ (i : V) (a : Matrix V V ℂ),
    ((Matrix.toEuclideanLin a (e i)) : EuclideanSpace ℂ V) =
      (aᵀ i) := fun _ _ => by
    simp only [Matrix.toEuclideanLin_apply']
    ext
    simp [Matrix.mulVec, dotProduct, e, Matrix.transpose_apply]
  constructor
  ext1 x
  simp only [schurMul_apply_apply, LinearMap.coe_comp, Function.comp_apply,
    EuclideanSpace.comul_eq, ← he]
  simp_rw [map_sum, LinearMapClass.map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply]
  ext1 j
  simp [this, Matrix.mulVec, dotProduct, Matrix.transpose_apply, SimpleGraph.adjMatrix,
    Matrix.of_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ← ite_and, and_self]

theorem quantumGraph_numOfEdges_of_classical
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  QuantumGraph.NumOfEdges (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G))
    = ∑ i, ∑ j, SimpleGraph.adjMatrix ℂ G i j := by
  have hOne : ∀ i : V, (1 : EuclideanSpace ℂ V) i = (1 : ℂ) := fun i => rfl
  simp [QuantumGraph.NumOfEdges, Matrix.mulVec, dotProduct, PiLp.inner_apply, hOne]

theorem SimpleGraph.conjTranspose_adjMatrix {V α : Type*} (G : SimpleGraph V)
  [DecidableRel G.Adj] [NonAssocSemiring α] [StarRing α] :
  (SimpleGraph.adjMatrix α G)ᴴ = SimpleGraph.adjMatrix α G := by
  ext
  simp [star_ite, star_one, star_zero, adj_comm]

theorem SimpleGraph.adjMatrix_toEuclideanLin_isReal
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  LinearMap.IsReal (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G)) := by
  intro
  ext
  simp [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix, Matrix.of_apply]

theorem SimpleGraph.adjMatrix_toEuclideanLin_symmMap
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  symmMap ℂ _ _ (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G))
    = Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G) := by
  simp only [symmMap_apply,
    LinearMap.real_of_isReal (SimpleGraph.adjMatrix_toEuclideanLin_isReal G),
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    SimpleGraph.conjTranspose_adjMatrix]

theorem SimpleGraph.adjMatrix_irreflexive
  {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  (Matrix.toEuclideanLin (SimpleGraph.adjMatrix ℂ G)) •ₛ 1 = 0 := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  ext1 x
  simp only [schurMul_apply_apply, LinearMap.comp_apply]
  rw [EuclideanSpace.comul_eq]
  simp only [map_sum, map_smul, TensorProduct.map_tmul, LinearMap.mul'_apply,
    Module.End.one_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, SimpleGraph.adjMatrix, Matrix.of_apply, Pi.single_apply,
    SimpleGraph.irrefl]
