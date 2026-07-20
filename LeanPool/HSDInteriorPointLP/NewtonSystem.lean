/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/

import LeanPool.HSDInteriorPointLP.PrimalDualData

/-!
# Newton-system layer

This file connects the HSDE/HLP equations with the Newton direction used in the
interior-point proof.  Conceptually, this is the linear-algebra layer: the later
algorithm file should not need to know the details of the Newton matrix.

Lean-reading hints for beginners:
* `intro h` proves an implication or a universal statement by introducing its
  premise/variable as the local name `h`.
* `have h : P := by ...` creates an intermediate lemma named `h`.
* `rcases h with ⟨a, b, c⟩` decomposes a conjunction/existential proof into its
  components.
* `simpa [defs] using h` means: simplify the goal and the type of `h` using
  `defs`, then close the goal by `h`.
-/
noncomputable section

open scoped BigOperators

namespace HSDInteriorPointLP

/-!
## Short Lean proof-command guide

The file is written for readers who know the interior-point algebra but may be new
to Lean.

* `intro` introduces an assumption or quantified variable from the current goal.
* `have h : P := by ...` proves and names an intermediate claim.
* `rcases h with ⟨...⟩` unpacks conjunctions, existentials, and structures.
* `simp only [...]` performs controlled rewriting using only the listed facts.
* `simpa [defs] using h` simplifies the goal and the type of `h`, then applies `h`.
* `linarith` closes linear real-arithmetic goals from the available hypotheses.
* `nlinarith` is the same idea for nonlinear arithmetic such as products/squares.
* `ring` proves polynomial identities over rings such as `ℝ`.
-/

/-!
# Active HLP/YTM proof layer

This file contains the parts that are still under active proof engineering:

* the full Newton block operator and its finite-dimensional solvability proof;
* Schur-complement complementarity arguments;
* the remaining YTM predictor/corrector local estimates.

The stable definitions and elementary lemmas are imported from
`HSDInteriorPointLP.PrimalDualData`.
-/


/-- Pull a scalar out of a finite sum.  This is the only finite-sum scalar rule
used below; the block-operator proof invokes it through `matVec`, `tMatVec`, and
`dot` scalar-multiplication lemmas, rather than by broad rewriting inside the
large product goal. -/
theorem finset_sum_smul_simple {ι : Type*} [Fintype ι]
    (a : ℝ) (f : ι → ℝ) :
    (∑ x : ι, a * f x) = a * ∑ x : ι, f x := by
  simpa using
    (Finset.mul_sum (s := (Finset.univ : Finset ι)) (f := f) (a := a)).symm

/-- Scalar multiplication in the vector argument of `matVec`. -/
theorem matVec_smul_apply {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (a : ℝ) (x : Vec n) (i : Fin m) :
    matVec A (fun j : Fin n => a * x j) i = a * matVec A x i := by
  unfold matVec
  calc
    (∑ j : Fin n, A i j * (a * x j))
        = ∑ j : Fin n, a * (A i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
    _ = a * ∑ j : Fin n, A i j * x j := by
            exact finset_sum_smul_simple a (fun j : Fin n => A i j * x j)

/-- Scalar multiplication in the vector argument of `tMatVec`. -/
theorem tMatVec_smul_apply {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (a : ℝ) (y : Vec m) (j : Fin n) :
    tMatVec A (fun i : Fin m => a * y i) j = a * tMatVec A y j := by
  unfold tMatVec
  calc
    (∑ i : Fin m, A i j * (a * y i))
        = ∑ i : Fin m, a * (A i j * y i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = a * ∑ i : Fin m, A i j * y i := by
            exact finset_sum_smul_simple a (fun i : Fin m => A i j * y i)

/-- Scalar multiplication in the second argument of `dot`. -/
theorem dot_smul_right {n : Nat} (u v : Vec n) (a : ℝ) :
    dot u (fun i : Fin n => a * v i) = a * dot u v := by
  unfold dot
  calc
    (∑ i : Fin n, u i * (a * v i))
        = ∑ i : Fin n, a * (u i * v i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = a * ∑ i : Fin n, u i * v i := by
            exact finset_sum_smul_simple a (fun i : Fin n => u i * v i)


/-- Component projections for scalar multiplication on the HLP block product space.  These
lemmas keep the Newton-block linearity proof away from broad `simp`. -/
@[simp] theorem HLPBlockSpace_smul_dy {m n : Nat} (a : ℝ) (u : HLPBlockSpace m n)
    (i : Fin m) : (a • u : HLPBlockSpace m n).1 i = a * u.1 i := rfl

@[simp] theorem HLPBlockSpace_smul_dx {m n : Nat} (a : ℝ) (u : HLPBlockSpace m n)
    (j : Fin n) : (a • u : HLPBlockSpace m n).2.1 j = a * u.2.1 j := rfl

@[simp] theorem HLPBlockSpace_smul_dtau {m n : Nat} (a : ℝ) (u : HLPBlockSpace m n) :
    (a • u : HLPBlockSpace m n).2.2.1 = a * u.2.2.1 := rfl

@[simp] theorem HLPBlockSpace_smul_dtheta {m n : Nat} (a : ℝ) (u : HLPBlockSpace m n) :
    (a • u : HLPBlockSpace m n).2.2.2.1 = a * u.2.2.2.1 := rfl

@[simp] theorem HLPBlockSpace_smul_ds {m n : Nat} (a : ℝ) (u : HLPBlockSpace m n)
    (j : Fin n) : (a • u : HLPBlockSpace m n).2.2.2.2.1 j = a * u.2.2.2.2.1 j := rfl

@[simp] theorem HLPBlockSpace_smul_dkappa {m n : Nat} (a : ℝ) (u : HLPBlockSpace m n) :
    (a • u : HLPBlockSpace m n).2.2.2.2.2 = a * u.2.2.2.2.2 := rfl

/-- Component projections for addition on the HLP block product space. -/
@[simp] theorem HLPBlockSpace_add_dy {m n : Nat} (u v : HLPBlockSpace m n)
    (i : Fin m) : (u + v : HLPBlockSpace m n).1 i = u.1 i + v.1 i := rfl

@[simp] theorem HLPBlockSpace_add_dx {m n : Nat} (u v : HLPBlockSpace m n)
    (j : Fin n) : (u + v : HLPBlockSpace m n).2.1 j = u.2.1 j + v.2.1 j := rfl

@[simp] theorem HLPBlockSpace_add_dtau {m n : Nat} (u v : HLPBlockSpace m n) :
    (u + v : HLPBlockSpace m n).2.2.1 = u.2.2.1 + v.2.2.1 := rfl

@[simp] theorem HLPBlockSpace_add_dtheta {m n : Nat} (u v : HLPBlockSpace m n) :
    (u + v : HLPBlockSpace m n).2.2.2.1 = u.2.2.2.1 + v.2.2.2.1 := rfl

@[simp] theorem HLPBlockSpace_add_ds {m n : Nat} (u v : HLPBlockSpace m n)
    (j : Fin n) : (u + v : HLPBlockSpace m n).2.2.2.2.1 j =
      u.2.2.2.2.1 j + v.2.2.2.2.1 j := rfl

@[simp] theorem HLPBlockSpace_add_dkappa {m n : Nat} (u v : HLPBlockSpace m n) :
    (u + v : HLPBlockSpace m n).2.2.2.2.2 = u.2.2.2.2.2 + v.2.2.2.2.2 := rfl

/-- The full Newton block operator as a linear self-map on the product block space. -/
def HLPNewtonBlockOperator {m n : Nat} (P : LPData m n) (w : HSState n) :
    HLPBlockSpace m n →ₗ[ℝ] HLPBlockSpace m n where
  toFun := fun u =>
    let D := HLPFullDirection.ofBlockVector u
    ( (fun i : Fin m =>
        matVec P.A D.dx i - P.b i * D.dtau + bbar P i * D.dtheta),
      (fun j : Fin n =>
        -(tMatVec P.A D.dy j) + P.c j * D.dtau - cbar P j * D.dtheta - D.ds j),
      dot P.b D.dy - dot P.c D.dx + zbar P * D.dtheta - D.dkappa,
      -(dot (bbar P) D.dy) + dot (cbar P) D.dx - zbar P * D.dtau,
      (fun j : Fin n => w.x j * D.ds j + w.s j * D.dx j),
      w.tau * D.dkappa + w.kappa * D.dtau )
  map_add' := by
    intro u v
    ext i <;>
      simp only [HLPFullDirection.ofBlockVector, matVec, tMatVec, dot, bbar, cbar,
        HLPBlockSpace_add_dy, HLPBlockSpace_add_dx, HLPBlockSpace_add_dtau,
        HLPBlockSpace_add_dtheta, HLPBlockSpace_add_ds, HLPBlockSpace_add_dkappa,
        Finset.sum_add_distrib, mul_add]
      <;> ring_nf
  map_smul' := by
    intro a u
    ext i
    · simp only [HLPFullDirection.ofBlockVector, HLPBlockSpace_smul_dtau,
        HLPBlockSpace_smul_dtheta, Prod.smul_mk, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      change
        matVec P.A (fun j : Fin n => a * u.2.1 j) i - P.b i * (a * u.2.2.1)
            + bbar P i * (a * u.2.2.2.1)
          = a * (matVec P.A u.2.1 i - P.b i * u.2.2.1
            + bbar P i * u.2.2.2.1)
      calc
        matVec P.A (fun j : Fin n => a * u.2.1 j) i - P.b i * (a * u.2.2.1)
            + bbar P i * (a * u.2.2.2.1)
            = a * matVec P.A u.2.1 i - P.b i * (a * u.2.2.1)
              + bbar P i * (a * u.2.2.2.1) := by
                simp only [matVec_smul_apply]
        _ = a * (matVec P.A u.2.1 i - P.b i * u.2.2.1
            + bbar P i * u.2.2.2.1) := by
                ring
    · simp only [HLPFullDirection.ofBlockVector, HLPBlockSpace_smul_dtau,
        HLPBlockSpace_smul_dtheta, HLPBlockSpace_smul_ds, Prod.smul_mk,
        Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      change
        -(tMatVec P.A (fun k : Fin m => a * u.1 k) i) + P.c i * (a * u.2.2.1)
            - cbar P i * (a * u.2.2.2.1) - a * u.2.2.2.2.1 i
          = a * (-(tMatVec P.A u.1 i) + P.c i * u.2.2.1
            - cbar P i * u.2.2.2.1 - u.2.2.2.2.1 i)
      calc
        -(tMatVec P.A (fun k : Fin m => a * u.1 k) i) + P.c i * (a * u.2.2.1)
            - cbar P i * (a * u.2.2.2.1) - a * u.2.2.2.2.1 i
            = -(a * tMatVec P.A u.1 i) + P.c i * (a * u.2.2.1)
              - cbar P i * (a * u.2.2.2.1) - a * u.2.2.2.2.1 i := by
                simp only [tMatVec_smul_apply]
        _ = a * (-(tMatVec P.A u.1 i) + P.c i * u.2.2.1
            - cbar P i * u.2.2.2.1 - u.2.2.2.2.1 i) := by
                ring
    · simp only [HLPFullDirection.ofBlockVector, HLPBlockSpace_smul_dtheta,
        HLPBlockSpace_smul_dkappa, Prod.smul_mk, smul_eq_mul, RingHom.id_apply]
      change
        dot P.b (fun k : Fin m => a * u.1 k) - dot P.c (fun j : Fin n => a * u.2.1 j)
            + zbar P * (a * u.2.2.2.1) - a * u.2.2.2.2.2
          = a * (dot P.b u.1 - dot P.c u.2.1 + zbar P * u.2.2.2.1
            - u.2.2.2.2.2)
      calc
        dot P.b (fun k : Fin m => a * u.1 k) - dot P.c (fun j : Fin n => a * u.2.1 j)
            + zbar P * (a * u.2.2.2.1) - a * u.2.2.2.2.2
            = a * dot P.b u.1 - a * dot P.c u.2.1
              + zbar P * (a * u.2.2.2.1) - a * u.2.2.2.2.2 := by
                simp only [dot_smul_right]
        _ = a * (dot P.b u.1 - dot P.c u.2.1 + zbar P * u.2.2.2.1
            - u.2.2.2.2.2) := by
                ring
    · simp only [HLPFullDirection.ofBlockVector, HLPBlockSpace_smul_dtau,
        Prod.smul_mk, smul_eq_mul, RingHom.id_apply]
      change
        -(dot (bbar P) (fun k : Fin m => a * u.1 k))
            + dot (cbar P) (fun j : Fin n => a * u.2.1 j)
            - zbar P * (a * u.2.2.1)
          = a * (-(dot (bbar P) u.1) + dot (cbar P) u.2.1
            - zbar P * u.2.2.1)
      calc
        -(dot (bbar P) (fun k : Fin m => a * u.1 k))
            + dot (cbar P) (fun j : Fin n => a * u.2.1 j)
            - zbar P * (a * u.2.2.1)
            = -(a * dot (bbar P) u.1) + a * dot (cbar P) u.2.1
              - zbar P * (a * u.2.2.1) := by
                simp only [dot_smul_right]
        _ = a * (-(dot (bbar P) u.1) + dot (cbar P) u.2.1
            - zbar P * u.2.2.1) := by
                ring
    · simp only [HLPFullDirection.ofBlockVector, HLPBlockSpace_smul_dx,
        HLPBlockSpace_smul_ds, Prod.smul_mk, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring
    · simp only [HLPFullDirection.ofBlockVector, HLPBlockSpace_smul_dtau,
        HLPBlockSpace_smul_dkappa, Prod.smul_mk, smul_eq_mul, RingHom.id_apply]
      ring

/-- Zero residual of the block operator is exactly the homogeneous Newton block. -/
theorem HLPNewtonBlockOperator_eq_zero_iff_homogeneous {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n) :
    HLPNewtonBlockOperator P w (HLPFullDirection.toBlockVector D) = 0 ↔
      HLPNewtonHomogeneousBlockSystem P w D := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hi := congrArg (fun u : HLPBlockSpace m n => u.1 i) h
      simpa [HLPNewtonBlockOperator, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hi
    · intro j
      have hj := congrArg (fun u : HLPBlockSpace m n => u.2.1 j) h
      simpa [HLPNewtonBlockOperator, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hj
    · have hg := congrArg (fun u : HLPBlockSpace m n => u.2.2.1) h
      simpa [HLPNewtonBlockOperator, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hg
    · have hn := congrArg (fun u : HLPBlockSpace m n => u.2.2.2.1) h
      simpa [HLPNewtonBlockOperator, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hn
    · intro j
      have hc := congrArg (fun u : HLPBlockSpace m n => u.2.2.2.2.1 j) h
      simpa [HLPNewtonBlockOperator, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hc
    · have hs := congrArg (fun u : HLPBlockSpace m n => u.2.2.2.2.2) h
      simpa [HLPNewtonBlockOperator, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hs
  · intro h
    ext i <;>
      simp [HLPNewtonBlockOperator, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector, h.primal_block, h.dual_block, h.gap_block,
        h.normalizing_block, h.complementarity_block, h.scalar_complementarity_block]

/-- Hitting the inhomogeneous right-hand side is exactly solving the Newton block. -/
theorem HLPNewtonBlockOperator_eq_rhs_iff_block_system {m n : Nat}
    (P : LPData m n) (w : HSState n) (γ : ℝ) (D : HLPFullDirection m n) :
    HLPNewtonBlockOperator P w (HLPFullDirection.toBlockVector D)
        = HLPNewtonBlockRhs w γ m ↔
      HLPNewtonBlockSystem P w D γ := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hi := congrArg (fun u : HLPBlockSpace m n => u.1 i) h
      simpa [HLPNewtonBlockOperator, HLPNewtonBlockRhs, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hi
    · intro j
      have hj := congrArg (fun u : HLPBlockSpace m n => u.2.1 j) h
      simpa [HLPNewtonBlockOperator, HLPNewtonBlockRhs, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hj
    · have hg := congrArg (fun u : HLPBlockSpace m n => u.2.2.1) h
      simpa [HLPNewtonBlockOperator, HLPNewtonBlockRhs, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hg
    · have hn := congrArg (fun u : HLPBlockSpace m n => u.2.2.2.1) h
      simpa [HLPNewtonBlockOperator, HLPNewtonBlockRhs, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector] using hn
    · intro j
      have hc := congrArg (fun u : HLPBlockSpace m n => u.2.2.2.2.1 j) h
      simpa [HLPNewtonBlockOperator, HLPNewtonBlockRhs, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector, complRhs] using hc
    · have hs := congrArg (fun u : HLPBlockSpace m n => u.2.2.2.2.2) h
      simpa [HLPNewtonBlockOperator, HLPNewtonBlockRhs, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector, scalarComplRhs] using hs
  · intro h
    ext i <;>
      simp [HLPNewtonBlockOperator, HLPNewtonBlockRhs, HLPFullDirection.toBlockVector,
        HLPFullDirection.ofBlockVector, h.primal_block, h.dual_block, h.gap_block,
        h.normalizing_block, h.complementarity_block, h.scalar_complementarity_block,
        complRhs, scalarComplRhs]

/-- In a finite-dimensional vector space, an injective linear self-map is surjective. -/
theorem finiteDimensional_surjective_of_injective_self
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : V →ₗ[ℝ] V) (hinj : Function.Injective L) : Function.Surjective L := by
  classical
  exact (LinearMap.injective_iff_surjective).1 hinj

/-- The concrete HLP nullspace equations imply the reduced skew-operator
nullspace condition.  This is the explicit place where the skew-symmetry of the
YTM HLP coefficient matrix must be formalized. -/
theorem HLPNullDirection_from_full_nullspace {m n : Nat}
    (P : LPData m n) (D : HLPFullDirection m n)
    (hnull : HLPNullspaceEquations P D) :
    HLPNullDirection (HLPFullDirection.toHSDirection D) := by
  refine ⟨?_⟩
  have hds : ∀ j : Fin n,
      D.ds j = -(tMatVec P.A D.dy j) + P.c j * D.dtau - cbar P j * D.dtheta := by
    intro j
    have h := hnull.dual_eq j
    linarith
  have hdk : D.dkappa = dot P.b D.dy - dot P.c D.dx + zbar P * D.dtheta := by
    have h := hnull.gap_eq
    linarith
  have hprimal : ∀ i : Fin m,
      matVec P.A D.dx i = P.b i * D.dtau - bbar P i * D.dtheta := by
    intro i
    have h := hnull.primal_eq i
    linarith
  have hnorm : dot (bbar P) D.dy - dot (cbar P) D.dx + zbar P * D.dtau = 0 := by
    have h := hnull.normalizing_eq
    linarith
  have hdot_ds :
      dot D.dx D.ds
        = - dot D.dx (tMatVec P.A D.dy)
          + D.dtau * dot D.dx P.c
          - D.dtheta * dot D.dx (cbar P) := by
    unfold dot
    calc
      (∑ j : Fin n, D.dx j * D.ds j)
          = ∑ j : Fin n, D.dx j *
              (-(tMatVec P.A D.dy j) + P.c j * D.dtau - cbar P j * D.dtheta) := by
              simp_all
      _ = ∑ j : Fin n,
              (-(D.dx j * tMatVec P.A D.dy j)
                + D.dtau * (D.dx j * P.c j)
                - D.dtheta * (D.dx j * cbar P j)) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = - (∑ j : Fin n, D.dx j * tMatVec P.A D.dy j)
            + D.dtau * (∑ j : Fin n, D.dx j * P.c j)
            - D.dtheta * (∑ j : Fin n, D.dx j * cbar P j) := by
              rw [Finset.sum_sub_distrib]
              rw [Finset.sum_add_distrib]
              rw [Finset.sum_neg_distrib]
              rw [← Finset.mul_sum]
              rw [← Finset.mul_sum]
      _ = - dot D.dx (tMatVec P.A D.dy)
            + D.dtau * dot D.dx P.c
            - D.dtheta * dot D.dx (cbar P) := by
              rfl
  have hmat : dot D.dx (tMatVec P.A D.dy)
      = D.dtau * dot P.b D.dy - D.dtheta * dot (bbar P) D.dy := by
    calc
      dot D.dx (tMatVec P.A D.dy)
          = dot D.dy (matVec P.A D.dx) := by
              rw [dot_tMatVec_eq_dot_matVec]
      _ = dot D.dy (fun i => P.b i * D.dtau - bbar P i * D.dtheta) := by
              unfold dot
              simp_all
      _ = D.dtau * dot P.b D.dy - D.dtheta * dot (bbar P) D.dy := by
              unfold dot
              calc
                (∑ i : Fin m, D.dy i * (P.b i * D.dtau - bbar P i * D.dtheta))
                    = ∑ i : Fin m,
                        (D.dtau * (P.b i * D.dy i) - D.dtheta * (bbar P i * D.dy i)) := by
                        apply Finset.sum_congr rfl
                        intro i _
                        ring
                _ = D.dtau * (∑ i : Fin m, P.b i * D.dy i)
                    - D.dtheta * (∑ i : Fin m, bbar P i * D.dy i) := by
                        rw [Finset.sum_sub_distrib]
                        rw [← Finset.mul_sum]
                        rw [← Finset.mul_sum]
  have hnorm' : dot (bbar P) D.dy - dot D.dx (cbar P) + zbar P * D.dtau = 0 := by
    have hcbar_comm : dot D.dx (cbar P) = dot (cbar P) D.dx := by
      unfold dot
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_all
  have hc_comm : dot D.dx P.c = dot P.c D.dx := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold HLPFullDirection.toHSDirection hdot
  change dot D.dx D.ds + D.dtau * D.dkappa = 0
  calc
    dot D.dx D.ds + D.dtau * D.dkappa
        = D.dtheta * (dot (bbar P) D.dy - dot D.dx (cbar P) + zbar P * D.dtau) := by
            rw [hdot_ds, hdk, hmat, hc_comm]
            ring
    _ = 0 := by
            simp_all



/-! ### Schur-complement form of the homogeneous Newton-kernel proof

The following small definitions and lemmas make the proof of
`HLP_newton_block_kernel_trivial_from_full_row_rank` follow the standard Newton
matrix argument: eliminate `(ds, dκ)` by the positive diagonal complementarity block,
form the Schur complement in `(dy, dτ, dθ)`, first prove the Schur residual and
`dτ` vanish, and only then remove the remaining multiplier variables.
-/

/-- The Schur-complement residual
`r = Aᵀ dy - c dτ + cbar dθ`.  In the homogeneous dual block we have `ds = -r`. -/
def HLPSchurResidual {m n : Nat} (P : LPData m n) (D : HLPFullDirection m n) : Vec n :=
  fun j => tMatVec P.A D.dy j - P.c j * D.dtau + cbar P j * D.dtheta

/-- The positive diagonal ratio `Θ = S^{-1}X`, written componentwise. -/
def HLPThetaDiag {n : Nat} (w : HSState n) : Vec n :=
  fun j => w.x j / w.s j

/-- The homogeneous dual block gives `ds = -r`. -/
theorem HLPHomogeneous.ds_eq_neg_schurResidual {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n)
    (hD : HLPNewtonHomogeneousBlockSystem P w D) :
    ∀ j : Fin n, D.ds j = -HLPSchurResidual P D j := by
  intro j
  have h := hD.dual_block j
  unfold HLPSchurResidual
  linarith

/-- The scalar complementarity block eliminates `dκ`. -/
theorem HLPHomogeneous.dkappa_eq_neg_ratio_dtau {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n)
    (hw : Interior w) (hD : HLPNewtonHomogeneousBlockSystem P w D) :
    D.dkappa = -(w.kappa / w.tau) * D.dtau := by
  rcases hw with ⟨_hx, htau, _hs, _hkappa⟩
  have htau_ne : w.tau ≠ 0 := ne_of_gt htau
  have h := hD.scalar_complementarity_block
  field_simp [htau_ne] at h ⊢
  linarith

/-- The complementarity block and the eliminated dual slack give
`dx = Θ r`, the usual first step in forming the Schur complement. -/
theorem HLPHomogeneous.dx_eq_theta_mul_schurResidual {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n)
    (hw : Interior w) (hD : HLPNewtonHomogeneousBlockSystem P w D) :
    ∀ j : Fin n, D.dx j = HLPThetaDiag w j * HLPSchurResidual P D j := by
  intro j
  rcases hw with ⟨_hx, _htau, hs, _hkappa⟩
  have hs_ne : w.s j ≠ 0 := ne_of_gt (hs j)
  have hds := HLPHomogeneous.ds_eq_neg_schurResidual P w D hD j
  have hcomp := hD.complementarity_block j
  unfold HLPThetaDiag
  rw [hds] at hcomp
  field_simp [hs_ne]
  linarith

/-- Schur-complement complementarity identity.

After eliminating `ds`, `dx`, and `dκ` through the positive diagonal
complementarity block, the homogeneous HLP orthogonality relation becomes
`∑ᵢ (xᵢ/sᵢ) rᵢ² + (κ/τ) dτ² = 0`.
This is the finite-dimensional inner-product identity used in the standard
interior-point nonsingularity argument. -/
theorem HLPHomogeneous.schur_complementarity_identity {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n)
    (hw : Interior w) (hD : HLPNewtonHomogeneousBlockSystem P w D) :
    (∑ j : Fin n, HLPThetaDiag w j * (HLPSchurResidual P D j) ^ 2)
      + (w.kappa / w.tau) * D.dtau ^ 2 = 0 := by
  /-
  This is obtained by applying `HLPNullDirection_from_full_nullspace` to the first
  four homogeneous blocks, giving `dot dx ds + dτ dκ = 0`, then rewriting the
  complementarity block with `ds = -r`, `dx = Θ r`, and
  `dκ = -(κ/τ)dτ`.
  -/
  have hnull : HLPNullspaceEquations P D :=
    ⟨hD.primal_block, hD.dual_block, hD.gap_block, hD.normalizing_block⟩
  have hcross := (HLPNullDirection_from_full_nullspace P D hnull).cross_zero
  have hds := HLPHomogeneous.ds_eq_neg_schurResidual P w D hD
  have hdx := HLPHomogeneous.dx_eq_theta_mul_schurResidual P w D hw hD
  have hdk := HLPHomogeneous.dkappa_eq_neg_ratio_dtau P w D hw hD
  have hcross_reduced : dot D.dx D.ds + D.dtau * D.dkappa = 0 := by
    simpa [HLPFullDirection.toHSDirection, hdot] using hcross
  have hdot_ds :
      dot D.dx D.ds
        = - (∑ j : Fin n, HLPThetaDiag w j * (HLPSchurResidual P D j) ^ 2) := by
    unfold dot
    calc
      (∑ j : Fin n, D.dx j * D.ds j)
          = ∑ j : Fin n,
              (HLPThetaDiag w j * HLPSchurResidual P D j)
                * (-(HLPSchurResidual P D j)) := by
              simp_all
      _ = ∑ j : Fin n, -(HLPThetaDiag w j * (HLPSchurResidual P D j) ^ 2) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = - (∑ j : Fin n, HLPThetaDiag w j * (HLPSchurResidual P D j) ^ 2) := by
              rw [Finset.sum_neg_distrib]
  have hdtau_dkappa :
      D.dtau * D.dkappa = - (w.kappa / w.tau) * D.dtau ^ 2 := by
    rw [hdk]
    ring
  calc
    (∑ j : Fin n, HLPThetaDiag w j * (HLPSchurResidual P D j) ^ 2)
        + (w.kappa / w.tau) * D.dtau ^ 2
        = -(dot D.dx D.ds + D.dtau * D.dkappa) := by
            rw [hdot_ds, hdtau_dkappa]
            ring
    _ = 0 := by
            rw [hcross_reduced]
            ring

/-- A finite-dimensional positivity lemma for the reduced complementarity form.

If all diagonal Schur weights are strictly positive and `eta > 0`, then the identity
`∑ᵢ thetaᵢ rᵢ² + eta t² = 0` forces every residual component `rᵢ` and the scalar
`t` to vanish.  This is the positive-diagonal part of the interior-point
nonsingularity argument, rather than positive-definiteness of the whole
`(dy, dτ, dθ)` Schur matrix. -/
theorem finite_sum_pos_sq_plus_pos_sq_eq_zero {n : Nat}
    (theta r : Vec n) (eta t : ℝ)
    (htheta : ∀ j : Fin n, 0 < theta j) (heta : 0 < eta)
    (h : (∑ j : Fin n, theta j * (r j) ^ 2) + eta * t ^ 2 = 0) :
    (∀ j : Fin n, r j = 0) ∧ t = 0 := by
  have hsummand_nonneg : ∀ j : Fin n, 0 ≤ theta j * (r j) ^ 2 := by
    intro j
    exact mul_nonneg (le_of_lt (htheta j)) (sq_nonneg (r j))
  have hsum_nonneg : 0 ≤ ∑ j : Fin n, theta j * (r j) ^ 2 := by
    apply Finset.sum_nonneg
    simp_all
  have htail_nonneg : 0 ≤ eta * t ^ 2 := by
    exact mul_nonneg (le_of_lt heta) (sq_nonneg t)
  have hsum_zero : (∑ j : Fin n, theta j * (r j) ^ 2) = 0 := by
    nlinarith
  have htail_zero : eta * t ^ 2 = 0 := by
    nlinarith
  constructor
  · intro j
    have hzero_all :=
      (Finset.sum_eq_zero_iff_of_nonneg (by
        simp_all)).mp hsum_zero
    have hprod_zero : theta j * (r j) ^ 2 = 0 := by
      exact hzero_all j (Finset.mem_univ j)
    have hsquare_zero : (r j) ^ 2 = 0 := by
      exact (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt (htheta j))
    exact sq_eq_zero_iff.mp hsquare_zero
  · have ht_square_zero : t ^ 2 = 0 := by
      exact (mul_eq_zero.mp htail_zero).resolve_left (ne_of_gt heta)
    exact sq_eq_zero_iff.mp ht_square_zero

/-- The reduced complementarity identity forces the Schur residual and `dτ` to be
zero. -/
theorem HLPHomogeneous.schur_residual_zero_and_dtau_zero {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n)
    (hw : Interior w) (hD : HLPNewtonHomogeneousBlockSystem P w D) :
    (∀ j : Fin n, HLPSchurResidual P D j = 0) ∧ D.dtau = 0 := by
  have hschur := HLPHomogeneous.schur_complementarity_identity P w D hw hD
  rcases hw with ⟨hx, htau, hs, hkappa⟩
  have htheta_pos : ∀ j : Fin n, 0 < HLPThetaDiag w j := by
    intro j
    unfold HLPThetaDiag
    exact div_pos (hx j) (hs j)
  have heta_pos : 0 < w.kappa / w.tau := by
    exact div_pos hkappa htau
  exact finite_sum_pos_sq_plus_pos_sq_eq_zero
    (HLPThetaDiag w) (HLPSchurResidual P D) (w.kappa / w.tau) D.dtau
    htheta_pos heta_pos hschur

/-- Once the Schur residual and `dτ` vanish, the reduced primal and scalar directions
vanish. -/
theorem HLPHomogeneous.dx_dkappa_ds_zero_from_schur_core {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n)
    (hw : Interior w) (hD : HLPNewtonHomogeneousBlockSystem P w D)
    (hr : ∀ j : Fin n, HLPSchurResidual P D j = 0) (hdtau : D.dtau = 0) :
    (∀ j : Fin n, D.dx j = 0) ∧ (∀ j : Fin n, D.ds j = 0) ∧ D.dkappa = 0 := by
  constructor
  · intro j
    rw [HLPHomogeneous.dx_eq_theta_mul_schurResidual P w D hw hD j, hr j]
    ring
  constructor
  · intro j
    rw [HLPHomogeneous.ds_eq_neg_schurResidual P w D hD j, hr j]
    ring
  · rcases hw with ⟨_hx, htau, _hs, _hkappa⟩
    have htau_ne : w.tau ≠ 0 := ne_of_gt htau
    have h := hD.scalar_complementarity_block
    simp_all

/-- Final algebra after the Schur core has vanished: the definitions of `bbar`, `cbar`,
and `zbar` imply `dθ = 0`; then full row rank gives `dy = 0`. -/
theorem HLPHomogeneous.dtheta_dy_zero_from_schur_core {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (w : HSState n) (D : HLPFullDirection m n)
    (hD : HLPNewtonHomogeneousBlockSystem P w D)
    (hr : ∀ j : Fin n, HLPSchurResidual P D j = 0)
    (hdtau : D.dtau = 0)
    (hdx : ∀ j : Fin n, D.dx j = 0)
    (hdkappa : D.dkappa = 0) :
    D.dtheta = 0 ∧ ∀ i : Fin m, D.dy i = 0 := by
  /-
  Final Schur-complement algebra.

  At this point the Schur core has already proved `r = 0` and `dτ = 0`, and the
  complementarity block has already given `dx = 0` and `dκ = 0`.  We use only the
  remaining homogeneous HLP equations and the definitions
  `bbar = b - A e`, `cbar = c - e`, and `zbar = cᵀe + 1`.
  -/
  have hdx_c : dot P.c D.dx = 0 := by
    unfold dot
    simp_all
  have hdx_cbar : dot (cbar P) D.dx = 0 := by
    unfold dot
    simp_all
  have hgap : dot P.b D.dy + zbar P * D.dtheta = 0 := by
    have h := hD.gap_block
    simp_all
  have hnormalizing : dot (bbar P) D.dy = 0 := by
    have h := hD.normalizing_block
    simp_all
  have hbbar_expand :
      dot (bbar P) D.dy = dot P.b D.dy - dot (matVec P.A (ones : Vec n)) D.dy := by
    unfold dot bbar
    calc
      (∑ i : Fin m, (P.b i - matVec P.A (ones : Vec n) i) * D.dy i)
          = ∑ i : Fin m, (P.b i * D.dy i - matVec P.A (ones : Vec n) i * D.dy i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : Fin m, P.b i * D.dy i)
          - (∑ i : Fin m, matVec P.A (ones : Vec n) i * D.dy i) := by
              rw [Finset.sum_sub_distrib]
  have hb_eq_Ae : dot P.b D.dy = dot (matVec P.A (ones : Vec n)) D.dy := by
    linarith
  have hmat_comm :
      dot (matVec P.A (ones : Vec n)) D.dy
        = dot D.dy (matVec P.A (ones : Vec n)) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hAe_eq_At :
      dot (matVec P.A (ones : Vec n)) D.dy
        = dot (ones : Vec n) (tMatVec P.A D.dy) := by
    rw [hmat_comm]
    rw [← dot_tMatVec_eq_dot_matVec P.A D.dy (ones : Vec n)]
  have hb_eq_At : dot P.b D.dy = dot (ones : Vec n) (tMatVec P.A D.dy) := by
    rw [hb_eq_Ae, hAe_eq_At]
  have hr_reduced : ∀ j : Fin n,
      tMatVec P.A D.dy j + cbar P j * D.dtheta = 0 := by
    intro j
    have h := hr j
    unfold HLPSchurResidual at h
    simp_all
  have hdual_sum :
      dot (ones : Vec n) (tMatVec P.A D.dy)
        + dot (ones : Vec n) (cbar P) * D.dtheta = 0 := by
    unfold dot ones
    have hsum :
        (∑ j : Fin n, (tMatVec P.A D.dy j + cbar P j * D.dtheta)) = 0 := by
      simp_all
    calc
      (∑ j : Fin n, 1 * tMatVec P.A D.dy j)
          + (∑ j : Fin n, 1 * cbar P j) * D.dtheta
          = (∑ j : Fin n, tMatVec P.A D.dy j)
              + (∑ j : Fin n, cbar P j * D.dtheta) := by
              simp [Finset.sum_mul]
      _ = (∑ j : Fin n, (tMatVec P.A D.dy j + cbar P j * D.dtheta)) := by
              rw [Finset.sum_add_distrib]
      _ = 0 := hsum
  have hdual_b :
      dot P.b D.dy + dot (ones : Vec n) (cbar P) * D.dtheta = 0 := by
    simp_all
  have hcoef_mul :
      (zbar P - dot (ones : Vec n) (cbar P)) * D.dtheta = 0 := by
    have hsub : zbar P * D.dtheta - dot (ones : Vec n) (cbar P) * D.dtheta = 0 := by
      linarith
    calc
      (zbar P - dot (ones : Vec n) (cbar P)) * D.dtheta
          = zbar P * D.dtheta - dot (ones : Vec n) (cbar P) * D.dtheta := by
              ring
      _ = 0 := hsub
  have hcoef : zbar P - dot (ones : Vec n) (cbar P) = (n : ℝ) + 1 := by
    unfold zbar cbar dot ones
    simp [Finset.sum_sub_distrib]
    ring
  have hcoef_pos : 0 < zbar P - dot (ones : Vec n) (cbar P) := by
    rw [hcoef]
    positivity
  have hdtheta : D.dtheta = 0 := by
    exact (mul_eq_zero.mp hcoef_mul).resolve_left (ne_of_gt hcoef_pos)
  have hAt_zero : ∀ j : Fin n, tMatVec P.A D.dy j = 0 := by
    simp_all
  have hrow_comb : ∀ j : Fin n, ∑ i : Fin m, D.dy i * P.A i j = 0 := by
    intro j
    have h := hAt_zero j
    unfold tMatVec at h
    calc
      (∑ i : Fin m, D.dy i * P.A i j)
          = ∑ i : Fin m, P.A i j * D.dy i := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 0 := h
  exact ⟨hdtheta, std.full_row_rank D.dy hrow_comb⟩

/-- Kernel triviality of the full HLP Newton block operator.

This is the part where the proof should use:

* full row rank of `A`,
* strict positivity of `x`, `tau`, `s`, and `kappa`,
* the skew-symmetric HLP block identities.

Mathematically, one first eliminates `ds` and `dκ` using the complementarity
blocks.  With `r = Aᵀdy - c dτ + cbar dθ`, this gives `dx = Θ r`, where
`Θ = S^{-1}X` is positive diagonal.  The Schur-complement identity is then
`∑ᵢ Θᵢ rᵢ² + (κ/τ)dτ² = 0`, so `r = 0` and `dτ = 0`.  The remaining HLP equations,
together with the definitions of `bbar`, `cbar`, and `zbar`, give `dθ = 0`, and full
row rank removes `dy`. -/
theorem HLP_newton_block_kernel_trivial_from_full_row_rank {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (w : HSState n) (hw : Interior w) :
    ∀ D : HLPFullDirection m n,
      HLPNewtonHomogeneousBlockSystem P w D →
      (∀ i, D.dx i = 0) ∧ D.dtau = 0 ∧ (∀ i, D.ds i = 0) ∧ D.dkappa = 0 ∧
      (∀ i, D.dy i = 0) ∧ D.dtheta = 0 := by
  intro D hD
  obtain ⟨hr, hdtau⟩ := HLPHomogeneous.schur_residual_zero_and_dtau_zero P w D hw hD
  obtain ⟨hdx, hds, hdkappa⟩ :=
    HLPHomogeneous.dx_dkappa_ds_zero_from_schur_core P w D hw hD hr hdtau
  obtain ⟨hdtheta, hdy⟩ :=
    HLPHomogeneous.dtheta_dy_zero_from_schur_core P std w D hD hr hdtau hdx hdkappa
  exact ⟨hdx, hdtau, hds, hdkappa, hdy, hdtheta⟩

/-- Finite-dimensional square linear systems: zero kernel implies solvability.

The HLP Newton block system is square.  Once the homogeneous block operator has
trivial kernel, finite-dimensional linear algebra gives surjectivity, hence existence of
a solution for the inhomogeneous Newton right-hand side. -/
theorem HLP_newton_block_system_solvable_from_kernel_trivial {m n : Nat}
    (P : LPData m n) (w : HSState n) (γ : ℝ)
    (hker : ∀ D : HLPFullDirection m n,
      HLPNewtonHomogeneousBlockSystem P w D →
      (∀ i, D.dx i = 0) ∧ D.dtau = 0 ∧ (∀ i, D.ds i = 0) ∧ D.dkappa = 0 ∧
      (∀ i, D.dy i = 0) ∧ D.dtheta = 0) :
    ∃ D : HLPFullDirection m n, HLPNewtonBlockSystem P w D γ := by
  classical
  let L : HLPBlockSpace m n →ₗ[ℝ] HLPBlockSpace m n := HLPNewtonBlockOperator P w
  have hker_op : ∀ u : HLPBlockSpace m n, L u = 0 → u = 0 := by
    intro u hu
    let D : HLPFullDirection m n := HLPFullDirection.ofBlockVector u
    have hhom : HLPNewtonHomogeneousBlockSystem P w D := by
      have huD : L (HLPFullDirection.toBlockVector D) = 0 := by
        simpa [L, D] using hu
      exact (HLPNewtonBlockOperator_eq_zero_iff_homogeneous P w D).1 huD
    rcases hker D hhom with ⟨hdx, hdtau, hds, hdkappa, hdy, hdtheta⟩
    rcases u with ⟨dy, dx, dtau, dtheta, ds, dkappa⟩
    change (dy, dx, dtau, dtheta, ds, dkappa) = (0, 0, 0, 0, 0, 0)
    apply Prod.ext
    · funext i
      exact hdy i
    · apply Prod.ext
      · funext i
        exact hdx i
      · apply Prod.ext
        · exact hdtau
        · apply Prod.ext
          · exact hdtheta
          · apply Prod.ext
            · funext i
              exact hds i
            · exact hdkappa
  have hinj : Function.Injective L := by
    intro u v huv
    have hsub : L (u - v) = 0 := by
      simpa [map_sub] using congrArg (fun y => y - L v) huv
    have hzero := hker_op (u - v) hsub
    exact sub_eq_zero.mp hzero
  have hsurj : Function.Surjective L :=
    finiteDimensional_surjective_of_injective_self L hinj
  rcases hsurj (HLPNewtonBlockRhs w γ m) with ⟨u, hu⟩
  let D : HLPFullDirection m n := HLPFullDirection.ofBlockVector u
  refine ⟨D, ?_⟩
  have huD : L (HLPFullDirection.toBlockVector D) = HLPNewtonBlockRhs w γ m := by
    simpa [L, D] using hu
  exact (HLPNewtonBlockOperator_eq_rhs_iff_block_system P w γ D).1 huD

/-- Concrete nonsingularity/surjectivity statement for the full HLP Newton block
system.  This is now the only finite-dimensional linear-algebra theorem that remains
for search-direction existence.

Mathematically, this is proved by eliminating `ds` and `dκ` with the positive diagonal
coefficients `xᵢ` and `τ`, and then using full row rank of `A` together with the
self-dual/skew-symmetric HLP block structure. -/
theorem HLP_newton_block_system_solvable_from_full_row_rank {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (w : HSState n) (hw : Interior w) (γ : ℝ) :
    ∃ D : HLPFullDirection m n, HLPNewtonBlockSystem P w D γ := by
  have hker := HLP_newton_block_kernel_trivial_from_full_row_rank P std w hw
  exact HLP_newton_block_system_solvable_from_kernel_trivial P w γ hker

/-- A full HLP direction equation gives the reduced direction equation used by the
rest of the proof skeleton. -/
theorem reduced_direction_equation_from_full {m n : Nat}
    (P : LPData m n) (w : HSState n) (D : HLPFullDirection m n) (γ : ℝ)
    (hD : HLPFullDirectionEquation P w D γ) :
    HSDDirectionEquation w (HLPFullDirection.toHSDirection D) γ := by
  refine ⟨?_, ?_, ?_⟩
  · exact HLPNullDirection_from_full_nullspace P D hD.null_eqs
  · intro i
    exact hD.component_eq i
  · exact hD.scalar_eq

/-- Concrete full HLP Newton linear-algebra theorem.

This is stronger and more explicit than the reduced `HLPNewtonLinearAlgebra`: it
states solvability of the full YTM direction system containing `dy` and `dθ`.
The proof should use the full-row-rank assumption on `A` and the positive diagonal
terms from the interior iterate. -/
structure HLPFullNewtonLinearAlgebra {m n : Nat} (P : LPData m n) : Prop where
  full_direction_system_solvable :
    LPStandardAssumptions P →
    ∀ (w : HSState n), Interior w → ∀ (γ : ℝ), ∃ D : HLPFullDirection m n,
      HLPFullDirectionEquation P w D γ

/-- Main concrete Newton solvability obligation for the YTM HLP system. -/
theorem HLP_full_newton_linear_algebra_from_full_row_rank {m n : Nat}
    (P : LPData m n)
    (std : LPStandardAssumptions P) :
    HLPFullNewtonLinearAlgebra P := by
  refine ⟨?_⟩
  intro _std w hw γ
  rcases HLP_newton_block_system_solvable_from_full_row_rank P std w hw γ with ⟨D, hDblock⟩
  exact ⟨D, (full_direction_equation_iff_block_system P w D γ).2 hDblock⟩

/-- Summing the componentwise complementarity equations, including the scalar
`τκ` equation, gives the aggregate first-order gap identity. -/
theorem aggregate_eq_from_component_eq {n : Nat}
    (w : HSState n) (d : HSDirection n) (γ : ℝ)
    (hcomp : ∀ i,
      w.x i * d.ds i + w.s i * d.dx i = γ * mu w - w.x i * w.s i)
    (hscalar :
      w.tau * d.dkappa + w.kappa * d.dtau = γ * mu w - w.tau * w.kappa) :
    hdot w.x w.tau d.ds d.dkappa + hdot d.dx d.dtau w.s w.kappa
      = -(1 - γ) * gap w := by
  have hleftVec :
      dot w.x d.ds + dot d.dx w.s =
        ∑ i, (w.x i * d.ds i + w.s i * d.dx i) := by
    unfold dot
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hrightVec :
      (∑ i, (w.x i * d.ds i + w.s i * d.dx i)) =
        ∑ i, (γ * mu w - w.x i * w.s i) := by
    simp_all
  have hsum_const :
      (∑ _i : Fin n, γ * mu w) = (n : ℝ) * (γ * mu w) := by
    simp_all
  have hsum_gap_vec :
      (∑ i, w.x i * w.s i) = dot w.x w.s := by
    rfl
  have hmu : hdim n * mu w = gap w := by
    unfold mu hdim
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp [ne_of_gt hpos]
  calc
    hdot w.x w.tau d.ds d.dkappa + hdot d.dx d.dtau w.s w.kappa
        = (dot w.x d.ds + dot d.dx w.s)
          + (w.tau * d.dkappa + w.kappa * d.dtau) := by
            unfold hdot
            ring
    _ = (∑ i, (w.x i * d.ds i + w.s i * d.dx i))
          + (w.tau * d.dkappa + w.kappa * d.dtau) := by
            rw [hleftVec]
    _ = (∑ i, (γ * mu w - w.x i * w.s i))
          + (γ * mu w - w.tau * w.kappa) := by
            rw [hrightVec, hscalar]
    _ = ((∑ _i : Fin n, γ * mu w) - ∑ i, w.x i * w.s i)
          + (γ * mu w - w.tau * w.kappa) := by
            rw [← Finset.sum_sub_distrib]
    _ = ((n : ℝ) * (γ * mu w) - dot w.x w.s)
          + (γ * mu w - w.tau * w.kappa) := by
            rw [hsum_const, hsum_gap_vec]
    _ = γ * (hdim n * mu w) - gap w := by
            unfold gap hdot hdim
            ring
    _ = -(1 - γ) * gap w := by
            rw [hmu]
            ring

/-- The skew-symmetry consequence is derived from the bundled HLP nullspace
relation.  This is the separated-variable version of Theorem 5(ii) in YTM. -/
theorem skew_orthogonal_from_HLP_nullspace {n : Nat}
    (d : HSDirection n) (hQ : HLPNullDirection d) :
    HSDSkewOrthogonal d := by
  exact ⟨hQ.cross_zero⟩

/-- The componentwise search-direction equation implies the aggregate
complementarity equation. -/
theorem complementarity_direction_from_equation {n : Nat}
    (w : HSState n) (d : HSDirection n) (γ : ℝ)
    (heq : HSDDirectionEquation w d γ) :
    HSDComplementarityDirection w d γ := by
  refine ⟨heq.component_eq, heq.scalar_eq, ?_⟩
  exact aggregate_eq_from_component_eq w d γ heq.component_eq heq.scalar_eq

/-- A solution of the HLP search-direction system gives a valid step direction. -/
theorem step_direction_from_direction_equation {n : Nat}
    (w : HSState n) (d : HSDirection n) (γ : ℝ)
    (heq : HSDDirectionEquation w d γ) :
    HSDStepDirection w d γ := by
  refine ⟨heq.null_dir, ?_, ?_⟩
  · exact skew_orthogonal_from_HLP_nullspace d heq.null_dir
  · exact complementarity_direction_from_equation w d γ heq

/-- Linear-algebra theorem needed for the YTM/HLP Newton system.

This packages the remaining finite-dimensional linear-algebra task: from the concrete
HLP Newton matrix and the full-row-rank assumption on `A`, one proves that the
predictor/corrector direction equations are solvable at every interior iterate.

The theorem is kept as an explicit field rather than hidden inside the algorithm.
In a later file, this should be replaced by an actual matrix nonsingularity proof. -/
structure HLPNewtonLinearAlgebra {m n : Nat} (P : LPData m n) : Prop where
  direction_system_solvable :
    LPStandardAssumptions P →
    ∀ (w : HSState n), Interior w → ∀ (γ : ℝ), ∃ d : HSDirection n, HSDDirectionEquation w d γ

/-- The concrete full Newton linear algebra induces the reduced linear algebra used
by the existing convergence skeleton. -/
theorem reduced_newton_linear_algebra_from_full {m n : Nat}
    (P : LPData m n)
    (fullAlg : HLPFullNewtonLinearAlgebra P) :
    HLPNewtonLinearAlgebra P := by
  refine ⟨?_⟩
  intro std w hw γ
  rcases fullAlg.full_direction_system_solvable std w hw γ with ⟨D, hD⟩
  exact ⟨HLPFullDirection.toHSDirection D, reduced_direction_equation_from_full P w D γ hD⟩

/-- Main finite-dimensional linear-algebra obligation for the HLP Newton system.

This is the place where the full-row-rank assumption on `A` should be used to prove
that the concrete Ye--Todd--Mizuno Newton system has a solution at each interior
iterate.  The current skeleton routes this obligation through the explicit full-system
solvability statement above. -/
theorem HLP_newton_linear_algebra_from_full_row_rank {m n : Nat}
    (P : LPData m n)
    (std : LPStandardAssumptions P) :
    HLPNewtonLinearAlgebra P := by
  refine ⟨?_⟩
  intro std' w hw γ
  have fullAlg : HLPFullNewtonLinearAlgebra P :=
    HLP_full_newton_linear_algebra_from_full_row_rank P std
  exact (reduced_newton_linear_algebra_from_full P fullAlg).direction_system_solvable std' w hw γ

/-- Solvability of the YTM/HLP Newton system at a given point and parameter. -/
structure HLPDirectionSystemSolvable {n : Nat}
    (w : HSState n) (γ : ℝ) : Prop where
  exists_direction : ∃ d : HSDirection n, HSDDirectionEquation w d γ

/-- Full-row-rank linear algebra supplies a solution of the search-direction system. -/
theorem direction_system_solvable_from_full_row_rank {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (linAlg : HLPNewtonLinearAlgebra P)
    (w : HSState n) (hw : Interior w) (γ : ℝ) :
    HLPDirectionSystemSolvable w γ := by
  exact ⟨linAlg.direction_system_solvable std w hw γ⟩

/-- Once solvability of the HLP Newton system is available, existence of a search
direction is immediate. -/
theorem search_direction_exists_from_HLP_solvability {n : Nat}
    (w : HSState n) (γ : ℝ)
    (hsolv : HLPDirectionSystemSolvable w γ) :
    ∃ d : HSDirection n, HSDDirectionEquation w d γ :=
  hsolv.exists_direction

/-- A noncomputable selector for the search direction once existence is known. -/
noncomputable def chooseSearchDirection {n : Nat}
    (w : HSState n) (γ : ℝ)
    (hex : ∃ d : HSDirection n, HSDDirectionEquation w d γ) : HSDirection n :=
  Classical.choose hex

/-- The selected search direction satisfies the search-direction equations. -/
theorem chooseSearchDirection_spec {n : Nat}
    (w : HSState n) (γ : ℝ)
    (hex : ∃ d : HSDirection n, HSDDirectionEquation w d γ) :
    HSDDirectionEquation w (chooseSearchDirection w γ hex) γ :=
  Classical.choose_spec hex

/-- The selected search direction is a valid step direction. -/
theorem chosen_step_direction {n : Nat}
    (w : HSState n) (γ : ℝ)
    (hex : ∃ d : HSDirection n, HSDDirectionEquation w d γ) :
    HSDStepDirection w (chooseSearchDirection w γ hex) γ := by
  exact step_direction_from_direction_equation w (chooseSearchDirection w γ hex) γ
    (chooseSearchDirection_spec w γ hex)

/-- Linearity of a finite sum with respect to the update `v + α dv`. -/
theorem sum_mul_add_smul {n : Nat}
    (u v dv : Vec n) (α : ℝ) :
    (∑ i, u i * (v i + α * dv i)) =
      (∑ i, u i * v i) + α * (∑ i, u i * dv i) := by
  calc
    (∑ i, u i * (v i + α * dv i))
        = ∑ i, (u i * v i + α * (u i * dv i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (∑ i, u i * v i) + ∑ i, α * (u i * dv i) := by
            rw [Finset.sum_add_distrib]
    _ = (∑ i, u i * v i) + α * (∑ i, u i * dv i) := by
            rw [Finset.mul_sum]

/-- Linearity of the second argument of `dot` for the update `v + α dv`. -/
theorem dot_add_smul {n : Nat} (u v dv : Vec n) (α : ℝ) :
    dot u (fun i => v i + α * dv i) = dot u v + α * dot u dv := by
  unfold dot
  exact sum_mul_add_smul u v dv α

theorem dot_comm {n : Nat} (u v : Vec n) :
    dot u v = dot v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Linearity of the first argument of `dot` for the update `u + α du`. -/
theorem dot_add_smul_left {n : Nat} (u du v : Vec n) (α : ℝ) :
    dot (fun i => u i + α * du i) v = dot u v + α * dot du v := by
  calc
    dot (fun i => u i + α * du i) v
        = dot v (fun i => u i + α * du i) := by
            rw [dot_comm]
    _ = dot v u + α * dot v du := by
            rw [dot_add_smul]
    _ = dot u v + α * dot du v := by
            rw [dot_comm v u, dot_comm v du]

/-- Expansion of `dot (u + α du) (v + α dv)`. -/
theorem dot_pair_add_smul {n : Nat}
    (u v du dv : Vec n) (α : ℝ) :
    dot (fun i => u i + α * du i) (fun i => v i + α * dv i) =
      dot u v + α * (dot du v + dot u dv) + α ^ 2 * dot du dv := by
  calc
    dot (fun i => u i + α * du i) (fun i => v i + α * dv i)
        = dot (fun i => u i + α * du i) v
          + α * dot (fun i => u i + α * du i) dv := by
            rw [dot_add_smul]
    _ = (dot u v + α * dot du v)
          + α * (dot u dv + α * dot du dv) := by
            rw [dot_add_smul_left u du v α]
            rw [dot_add_smul_left u du dv α]
    _ = dot u v + α * (dot du v + dot u dv) + α ^ 2 * dot du dv := by
            ring

/-- Algebraic expansion of the complementarity gap under a line step. -/
theorem gap_addStep_expansion {n : Nat}
    (w : HSState n) (d : HSDirection n) (α : ℝ) :
    gap (addStep w d α)
      = gap w + α * (hdot w.x w.tau d.ds d.dkappa + hdot d.dx d.dtau w.s w.kappa)
        + α ^ 2 * hdot d.dx d.dtau d.ds d.dkappa := by
  unfold gap addStep hdot
  rw [dot_pair_add_smul]
  ring_nf

/-- Gap update for a direction satisfying the HLP nullspace and complementarity equations. -/
theorem gap_addStep_of_HSDStepDirection {n : Nat}
    (w : HSState n) (d : HSDirection n) (α γ : ℝ)
    (hdir : HSDStepDirection w d γ) :
    gap (addStep w d α) = (1 - α * (1 - γ)) * gap w := by
  rw [gap_addStep_expansion]
  rw [hdir.compl.aggregate_eq]
  rw [hdir.skew.cross_zero]
  ring_nf

/-- Predictor step guarantee from the Mizuno--Todd--Ye local analysis. -/
structure PredictorStepGuarantee {n : Nat}
    (βwide c : ℝ) (w : HSState n) (d : HSDirection n) (α : ℝ) : Prop where
  alpha_pos : 0 < α
  alpha_le_one : α ≤ 1
  interior_next : Interior (addStep w d α)
  neighborhood_next : HSDNeighborhood βwide (addStep w d α)
  gap_decrease : gap (addStep w d α) ≤ (1 - c / Real.sqrt (hdim n)) * gap w

/-- Corrector step guarantee from the Mizuno--Todd--Ye local analysis. -/
structure CorrectorStepGuarantee {n : Nat}
    (βtight : ℝ) (w : HSState n) (d : HSDirection n) : Prop where
  interior_next : Interior (addStep w d 1)
  neighborhood_next : HSDNeighborhood βtight (addStep w d 1)
  gap_preserve : gap (addStep w d 1) = gap w



/-- The tight neighborhood parameter used in the YTM proof. -/
def ytmBetaTight : ℝ := 1 / 4

/-- The wide neighborhood parameter used in the YTM proof. -/
def ytmBetaWide : ℝ := 1 / 2

/-- The predictor step-size constant appearing in YTM Theorem 6.
Mathematically this is `8^{-2.5}`. -/
def ytmStepConstant : ℝ := 1 / ((8 : ℝ) ^ 2 * Real.sqrt 8)


/-! ### Corrector local estimate

The corrector half of the YTM local analysis is a componentwise estimate for the
full step.  In the usual notation, set

* `u = (x, τ)` and `v = (s, κ)`,
* `Δu = (dx, dτ)` and `Δv = (ds, dκ)`,
* `N = n + 1` and `μ = gap w / N`.

For a corrector direction (`γ = 1`), the linearized complementarity equations give

`uᵢ Δvᵢ + vᵢ Δuᵢ = μ - uᵢ vᵢ`,

and skew orthogonality gives `Σ Δuᵢ Δvᵢ = 0`.  The Mizuno--Todd--Ye
componentwise estimate proves that, if `w ∈ N(1/2)`, then the full corrector step
`w + d` is positive and lies in `N(1/4)`.  The proof is the standard scaled estimate

`‖Δu ∘ Δv‖ ≤ μ / 4`,

obtained by writing `pᵢ = Δuᵢ/uᵢ`, `qᵢ = Δvᵢ/vᵢ`,
`aᵢ = sqrt(uᵢvᵢ) pᵢ`, and `bᵢ = sqrt(uᵢvᵢ) qᵢ`.
This lemma is stated separately so that the top-level corrector theorem has exactly
the same shape as the IPM proof: local positivity/centrality estimate plus the
already-formalized gap identity. -/

end HSDInteriorPointLP
