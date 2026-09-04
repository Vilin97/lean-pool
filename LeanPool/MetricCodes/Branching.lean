/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Representation
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Harmonic Young branching

Trace ideals, Clebsch decompositions, and arbitrary-rank branching constructions.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungSameAxisTraceIdeal

open MetricCodes.Spherical.HigherHarmonicYoung

theorem homogeneousTraceFree_eq_iInf_ker {r n m : ℕ} :
    homogeneousTraceFreeSubmodule r n (m + 2) =
      ⨅ ij : Fin (r + 1) × Fin (r + 1),
        LinearMap.ker (homogeneousRowTrace (n := n) ij.1 ij.2 m) := by
  ext p
  simp only [mem_homogeneousTraceFreeSubmodule, Submodule.mem_iInf,
    LinearMap.mem_ker]
  constructor
  · intro h ij
    apply Subtype.ext
    exact h ij.1 ij.2
  · intro h i j
    exact congrArg (fun q : SpherePacking.Fischer.Homogeneous
      ((r + 1) * n) m => (q : PolynomialSpace r n)) (h (i, j))

theorem simultaneousHarmonicProjection_residual_mem_youngGramRadialIdeal
    {r n m : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) (m + 2)) :
    ((p : PolynomialSpace r n) -
      ((simultaneousHarmonicProjection r n (m + 2) p).val :
        PolynomialSpace r n)) ∈ youngGramRadialIdeal r n := by
  let E := SpherePacking.Fischer.Homogeneous ((r + 1) * n) m
  let F := SpherePacking.Fischer.Homogeneous ((r + 1) * n) (m + 2)
  let : InnerProductSpace.Core ℝ E :=
    SpherePacking.Fischer.homogeneousInnerCore ((r + 1) * n) m
  let : NormedAddCommGroup E :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ E :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ E)
  let : InnerProductSpace.Core ℝ F :=
    SpherePacking.Fischer.homogeneousInnerCore ((r + 1) * n) (m + 2)
  let : NormedAddCommGroup F :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ F :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ F)
  have hadjoint (i j : Fin (r + 1)) :
      (homogeneousRowTrace (n := n) i j m).adjoint =
        homogeneousRowPairingMultiplication (n := n) i j m := by
    symm
    apply (LinearMap.eq_adjoint_iff _ _).mpr
    intro a b
    change
      SpherePacking.Fischer.homogeneousInner ((r + 1) * n) (m + 2)
          (homogeneousRowPairingMultiplication i j m a) b =
        SpherePacking.Fischer.homogeneousInner ((r + 1) * n) m a
          (homogeneousRowTrace i j m b)
    rw [SpherePacking.Fischer.homogeneousInner_eq_polynomialInner,
      SpherePacking.Fischer.homogeneousInner_eq_polynomialInner,
      homogeneousRowPairingMultiplication_apply,
      homogeneousRowTrace_apply]
    exact polynomialInner_rowPairing_trace i j
      (a : PolynomialSpace r n) (b : PolynomialSpace r n)
  let residual : F :=
    p - (simultaneousHarmonicProjection r n (m + 2) p).val
  have horth : residual ∈ (homogeneousTraceFreeSubmodule r n (m + 2))ᗮ := by
    apply (Submodule.mem_orthogonal' _ _).mpr
    intro q hq
    change
      @inner ℝ F _
        (p - (simultaneousHarmonicProjection r n (m + 2) p).val) q = 0
    rw [inner_sub_left]
    change
      SpherePacking.Fischer.homogeneousInner ((r + 1) * n) (m + 2) p q -
        SpherePacking.Fischer.homogeneousInner ((r + 1) * n) (m + 2)
          (simultaneousHarmonicProjection r n (m + 2) p).val q = 0
    rw [SpherePacking.Fischer.homogeneousInner_eq_polynomialInner,
      SpherePacking.Fischer.homogeneousInner_eq_polynomialInner,
      simultaneousHarmonicProjection_polynomialInner p ⟨q, hq⟩]
    exact sub_self _
  rw [homogeneousTraceFree_eq_iInf_ker] at horth
  have hinf := Submodule.iInf_orthogonal
    (fun ij : Fin (r + 1) × Fin (r + 1) =>
      (LinearMap.ker (homogeneousRowTrace (n := n) ij.1 ij.2 m))ᗮ)
  simp_rw [Submodule.orthogonal_orthogonal] at hinf
  rw [hinf, Submodule.orthogonal_orthogonal] at horth
  simp_rw [LinearMap.orthogonal_ker, hadjoint] at horth
  have hle :
      (⨆ ij : Fin (r + 1) × Fin (r + 1),
        LinearMap.range
          (homogeneousRowPairingMultiplication (n := n) ij.1 ij.2 m)) ≤
      ((youngGramRadialIdeal r n).restrictScalars ℝ).comap
        (MvPolynomial.homogeneousSubmodule
          (Fin ((r + 1) * n)) ℝ (m + 2)).subtype := by
    apply iSup_le
    intro ij
    rintro _ ⟨q, rfl⟩
    exact (youngGramRadialIdeal r n).mul_mem_right
      (q : PolynomialSpace r n)
      (rowPairingPolynomial_mem_youngGramRadialIdeal ij.1 ij.2)
  exact hle horth

theorem simultaneousHarmonicProjection_eq_zero_iff_mem_youngGramRadialIdeal
    {r n m : ℕ}
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) (m + 2)) :
    simultaneousHarmonicProjection r n (m + 2) p = 0 ↔
      (p : PolynomialSpace r n) ∈ youngGramRadialIdeal r n := by
  constructor
  · intro hp
    have hresidual :=
      simultaneousHarmonicProjection_residual_mem_youngGramRadialIdeal p
    have hzero :
        (((simultaneousHarmonicProjection r n (m + 2) p).val :
          PolynomialSpace r n)) = 0 :=
      congrArg (fun q : homogeneousTraceFreeSubmodule r n (m + 2) =>
        (q.val : PolynomialSpace r n)) hp
    simpa only [hzero, sub_zero] using hresidual
  · intro hp
    apply Subtype.ext
    apply Subtype.ext
    apply (SpherePacking.Fischer.polynomialInner_self_eq_zero
      ((r + 1) * n)
      (((simultaneousHarmonicProjection r n (m + 2) p).val :
        PolynomialSpace r n))).mp
    calc
      SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (((simultaneousHarmonicProjection r n (m + 2) p).val :
            PolynomialSpace r n))
          (((simultaneousHarmonicProjection r n (m + 2) p).val :
            PolynomialSpace r n)) =
        SpherePacking.Fischer.polynomialInner ((r + 1) * n)
          (p : PolynomialSpace r n)
          (((simultaneousHarmonicProjection r n (m + 2) p).val :
            PolynomialSpace r n)) :=
        simultaneousHarmonicProjection_polynomialInner p
          (simultaneousHarmonicProjection r n (m + 2) p)
      _ = 0 :=
        polynomialInner_youngGramRadialIdeal_eq_zero_of_traceFree
          (((simultaneousHarmonicProjection r n (m + 2) p).val :
            PolynomialSpace r n)) (p : PolynomialSpace r n)
          (simultaneousHarmonicProjection_traceOperator p) hp

end HigherYoungSameAxisTraceIdeal

namespace HigherHarmonicYoung.ArbitraryRankHarmonicBranch

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherYoungBranchingFibres
open MetricCodes.Spherical.HigherYoungSameAxisTraceIdeal
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem simultaneousHarmonicProjection_eq_zero_iff_gramIdeal
    {r n d : ℕ} (hd : 2 ≤ d)
    (p : SpherePacking.Fischer.Homogeneous ((r + 1) * n) d) :
    simultaneousHarmonicProjection r n d p = 0 ↔
      (p : PolynomialSpace r n) ∈ youngGramRadialIdeal r n := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hd
  have hdm : d = m + 2 := by omega
  clear hm
  subst d
  exact simultaneousHarmonicProjection_eq_zero_iff_mem_youngGramRadialIdeal
    (r := r) (n := n) (m := m) p

/-- The harmonic branch of highest weight seed used in the spherical-code argument. -/
def harmonicBranchOfHighestWeightSeed
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (seed : E →ₗ[ℝ]
      homogeneousYoungHighestWeightSubmodule (n := n) lam) :
    E →ₗ[ℝ] HarmonicYoungSpace (n := n) lam :=
  (youngHarmonicLift lam).comp seed

end HigherHarmonicYoung.ArbitraryRankHarmonicBranch

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungProjectedRaiseInjectivity

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

theorem traceOperator_X_mul_coordinate {r n : ℕ}
    (a b row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    traceOperator r n a b
        (MvPolynomial.X (variableIndex row k) * p) =
      MvPolynomial.X (variableIndex row k) * traceOperator r n a b p +
        (if a = row then MvPolynomial.pderiv (variableIndex b k) p else 0) +
        (if b = row then MvPolynomial.pderiv (variableIndex a k) p else 0) := by
  classical
  simp only [traceOperator_apply, MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_X, Pi.single_apply,
    variableIndex_eq_iff_harmonicLift,
    map_add, Finset.sum_add_distrib]
  have hconstant (j : Fin n) :
      MvPolynomial.pderiv (variableIndex a j)
        (if row = b ∧ k = j then 1 else 0 : PolynomialSpace r n) = 0 := by
    split_ifs <;> simp
  simp only [hconstant, zero_mul, Finset.sum_const_zero, zero_add]
  have hbdelta :
      (∑ j : Fin n,
        (if row = b ∧ k = j then 1 else 0 : PolynomialSpace r n) *
          MvPolynomial.pderiv (variableIndex a j) p) =
        if b = row then MvPolynomial.pderiv (variableIndex a k) p else 0 := by
    by_cases hb : b = row
    · subst b
      simp only [true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte]
    · have hbr : row ≠ b := Ne.symm hb
      simp only [hbr, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero, hb]
  have hadelta :
      (∑ j : Fin n,
        (if row = a ∧ k = j then 1 else 0 : PolynomialSpace r n) *
          MvPolynomial.pderiv (variableIndex b j) p) =
        if a = row then MvPolynomial.pderiv (variableIndex b k) p else 0 := by
    by_cases ha : a = row
    · subst a
      simp only [true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        ↓reduceIte]
    · have har : row ≠ a := Ne.symm ha
      simp only [har, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero, ha]
  rw [hbdelta, hadelta, ← Finset.mul_sum]
  abel

end HigherYoungProjectedRaiseInjectivity

end

namespace HigherHarmonicYoung

section


open scoped BigOperators

theorem polarization_chain_commutator
    {r n : ℕ} (i j k : Fin (r + 1)) (hik : i ≠ k)
    (p : PolynomialSpace r n) :
    polarization r n i j (polarization r n j k p) =
      polarization r n i k p +
        polarization r n j k (polarization r n i j p) := by
  classical
  have hcross :
      (∑ a : Fin n,
        MvPolynomial.X (variableIndex i a) *
          polarization r n j k
            (MvPolynomial.pderiv (variableIndex j a) p)) =
        ∑ b : Fin n,
          MvPolynomial.X (variableIndex j b) *
            polarization r n i j
              (MvPolynomial.pderiv (variableIndex k b) p) := by
    simp_rw [polarization_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    rw [SpherePacking.mvPolynomial_pderiv_commute
      (variableIndex j a) (variableIndex k b) p]
    ring
  have hleft :
      polarization r n i j (polarization r n j k p) =
        polarization r n i k p +
          ∑ a : Fin n,
            MvPolynomial.X (variableIndex i a) *
              polarization r n j k
                (MvPolynomial.pderiv (variableIndex j a) p) := by
    rw [polarization_apply]
    simp_rw [pderiv_polarization_harmonicLift]
    simp only [↓reduceIte, polarization_apply, mul_add, Finset.sum_add_distrib]
  have hright :
      polarization r n j k (polarization r n i j p) =
        ∑ b : Fin n,
          MvPolynomial.X (variableIndex j b) *
            polarization r n i j
              (MvPolynomial.pderiv (variableIndex k b) p) := by
    rw [polarization_apply]
    simp_rw [pderiv_polarization_harmonicLift]
    have hki : k ≠ i := Ne.symm hik
    simp only [hki, ↓reduceIte, polarization_apply, zero_add]
  rw [hleft, hright, hcross]

theorem polarization_eq_zero_of_simpleRoots
    {r n : ℕ} (p : PolynomialSpace r n)
    (hsimple : ∀ a : Fin r,
      polarization r n a.castSucc a.succ p = 0)
    (i j : Fin (r + 1)) (hij : i < j) :
    polarization r n i j p = 0 := by
  induction hd : j.val - i.val using Nat.strong_induction_on
      generalizing i j with
  | h d ih =>
    by_cases hstep : j.val = i.val + 1
    · let a : Fin r := ⟨i.val, by omega⟩
      have hfirst : a.castSucc = i := Fin.ext rfl
      have hsecond : a.succ = j := by
        apply Fin.ext
        simpa [a] using hstep.symm
      simpa only [polarization_apply, hfirst, hsecond] using hsimple a
    · let k : Fin (r + 1) := ⟨i.val + 1, by omega⟩
      have hik : i < k := by
        change i.val < k.val
        dsimp [k]
        omega
      have hkj : k < j := by
        change k.val < j.val
        dsimp [k]
        omega
      have hshort : j.val - k.val < d := by
        dsimp [k]
        omega
      have htail : polarization r n k j p = 0 :=
        ih (j.val - k.val) hshort k j hkj rfl
      let a : Fin r := ⟨i.val, by omega⟩
      have hfirst : a.castSucc = i := Fin.ext rfl
      have hsecond : a.succ = k := Fin.ext rfl
      have hhead : polarization r n i k p = 0 := by
        simpa only [polarization_apply, hfirst, hsecond] using hsimple a
      have hbracket := polarization_chain_commutator
        i k j (Fin.ne_of_lt hij) p
      rw [htail, map_zero, hhead, map_zero, add_zero] at hbracket
      exact hbracket.symm

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRankLowerRowBranching

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranch
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherYoungProjectedRaiseInjectivity

theorem polarization_polarization_commutator {r n : ℕ}
    (a b c d : Fin (r + 1)) (p : PolynomialSpace r n) :
    polarization r n a b (polarization r n c d p) =
      polarization r n c d (polarization r n a b p) +
        (if b = c then polarization r n a d p else 0) -
          (if d = a then polarization r n c b p else 0) := by
  classical
  have hcross :
      (∑ k : Fin n,
        MvPolynomial.X (variableIndex a k) *
          polarization r n c d
            (MvPolynomial.pderiv (variableIndex b k) p)) =
        ∑ l : Fin n,
          MvPolynomial.X (variableIndex c l) *
            polarization r n a b
              (MvPolynomial.pderiv (variableIndex d l) p) := by
    simp_rw [polarization_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    rw [SpherePacking.mvPolynomial_pderiv_commute
      (variableIndex b k) (variableIndex d l) p]
    ring
  have hleft :
      polarization r n a b (polarization r n c d p) =
        (if b = c then polarization r n a d p else 0) +
          ∑ k : Fin n,
            MvPolynomial.X (variableIndex a k) *
              polarization r n c d
                (MvPolynomial.pderiv (variableIndex b k) p) := by
    rw [polarization_apply]
    simp_rw [pderiv_polarization_harmonicLift, mul_add]
    rw [Finset.sum_add_distrib]
    by_cases hbc : b = c
    · simp only [hbc, ↓reduceIte, polarization_apply]
    · simp only [hbc, ↓reduceIte, mul_zero, Finset.sum_const_zero, polarization_apply, zero_add]
  have hright :
      polarization r n c d (polarization r n a b p) =
        (if d = a then polarization r n c b p else 0) +
          ∑ l : Fin n,
            MvPolynomial.X (variableIndex c l) *
              polarization r n a b
                (MvPolynomial.pderiv (variableIndex d l) p) := by
    rw [polarization_apply]
    simp_rw [pderiv_polarization_harmonicLift, mul_add]
    rw [Finset.sum_add_distrib]
    by_cases hda : d = a
    · simp only [hda, ↓reduceIte, polarization_apply]
    · simp only [hda, ↓reduceIte, mul_zero, Finset.sum_const_zero, polarization_apply, zero_add]
  rw [hleft, hright, hcross]
  abel

end ArbitraryRankLowerRowBranching

end

section


open scoped BigOperators InnerProductSpace

theorem rowAxisPolynomial_smul {r n : ℕ}
    (i : Fin (r + 1)) (c : ℝ)
    (v : SpherePacking.Euclidean n) :
    rowAxisPolynomial i (c • v) = c • rowAxisPolynomial i v := by
  rw [rowAxisPolynomial_eq_sum, rowAxisPolynomial_eq_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change
    MvPolynomial.C (c * v k) * MvPolynomial.X (variableIndex i k) =
      c • (MvPolynomial.C (v k) * MvPolynomial.X (variableIndex i k))
  rw [map_mul, MvPolynomial.C_mul']
  exact smul_mul_assoc c _ _

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace MultiplicityFreeClebsch

theorem youngClebschLower_adjoint_tmul {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1))
    (v : SpherePacking.Euclidean n)
    (q : HarmonicYoungSpace (n := n) mu) :
    (youngClebschLower mu lam hdeg row).adjoint
        (v ⊗ₜ[ℝ] q) =
      projectedCoordinateRaise lam mu hdeg row v q := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hv : (∑ j : Fin n, v j • b j) = v := by
    simpa [b] using b.sum_repr v
  calc
    (youngClebschLower mu lam hdeg row).adjoint (v ⊗ₜ[ℝ] q) =
        (youngClebschLower mu lam hdeg row).adjoint
          ((∑ j : Fin n, v j • b j) ⊗ₜ[ℝ] q) := by rw [hv]
    _ = ∑ j : Fin n,
        v j • (youngClebschLower mu lam hdeg row).adjoint
          (b j ⊗ₜ[ℝ] q) := by
      rw [TensorProduct.sum_tmul, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← TensorProduct.smul_tmul', map_smul]
    _ = ∑ j : Fin n,
        v j • projectedCoordinateRaise lam mu hdeg row (b j) q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [youngClebschLower_adjoint_basis_tmul]
    _ = projectedCoordinateRaiseAxis lam mu hdeg row q
          (∑ j : Fin n, v j • b j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      rfl
    _ = projectedCoordinateRaise lam mu hdeg row v q := by rw [hv]; rfl

end MultiplicityFreeClebsch

end

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace FullRankClebschProbabilities

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherYoungProjectedRaiseInjectivity
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherHarmonicYoung.MultiplicityFreeClebsch

theorem normalizedYoungClebschLower_adjoint_tmul
    {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschLower mu lam hdeg row p,
        youngClebschLower mu lam hdeg row q⟫_ℝ =
          c * ⟪p, q⟫_ℝ)
    (v : SpherePacking.Euclidean n)
    (q : HarmonicYoungSpace (n := n) mu) :
    (normalizedYoungClebschLower mu lam hdeg row c hc hgram).adjoint
        (v ⊗ₜ[ℝ] q) =
      (Real.sqrt c)⁻¹ •
        projectedCoordinateRaise lam mu hdeg row v q := by
  apply ext_inner_left ℝ
  intro w
  calc
    ⟪w, (normalizedYoungClebschLower mu lam hdeg row c hc hgram).adjoint
        (v ⊗ₜ[ℝ] q)⟫_ℝ =
      ⟪normalizedYoungClebschLower mu lam hdeg row c hc hgram w,
        v ⊗ₜ[ℝ] q⟫_ℝ :=
      LinearMap.adjoint_inner_right
        (normalizedYoungClebschLower mu lam hdeg row c hc hgram).toLinearMap
        w (v ⊗ₜ[ℝ] q)
    _ = (Real.sqrt c)⁻¹ *
      ⟪youngClebschLower mu lam hdeg row w, v ⊗ₜ[ℝ] q⟫_ℝ := by
      change
        ⟪((normalizedYoungClebschLower mu lam hdeg row c hc hgram).toLinearMap)
          w, v ⊗ₜ[ℝ] q⟫_ℝ = _
      rw [normalizedYoungClebschLower_toLinearMap,
        LinearMap.smul_apply, real_inner_smul_left]
    _ = (Real.sqrt c)⁻¹ *
      ⟪w, (youngClebschLower mu lam hdeg row).adjoint
        (v ⊗ₜ[ℝ] q)⟫_ℝ := by
      rw [← LinearMap.adjoint_inner_right]
      rfl
    _ = (Real.sqrt c)⁻¹ *
      ⟪w, projectedCoordinateRaise lam mu hdeg row v q⟫_ℝ := by
      rw [youngClebschLower_adjoint_tmul]
    _ = ⟪w, (Real.sqrt c)⁻¹ •
        projectedCoordinateRaise lam mu hdeg row v q⟫_ℝ :=
      (real_inner_smul_right _ _ _).symm

theorem normalizedYoungClebschRaise_adjoint_tmul
    {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1)) (c : ℝ) (hc : 0 < c)
    (hgram : ∀ p q : HarmonicYoungSpace (n := n) lam,
      ⟪youngClebschRaise mu lam hdeg row p,
        youngClebschRaise mu lam hdeg row q⟫_ℝ =
          c * ⟪p, q⟫_ℝ)
    (v : SpherePacking.Euclidean n)
    (q : HarmonicYoungSpace (n := n) mu) :
    (normalizedYoungClebschRaise mu lam hdeg row c hc hgram).adjoint
        (v ⊗ₜ[ℝ] q) =
      (Real.sqrt c)⁻¹ •
        projectedCoordinateLower lam mu hdeg row v q := by
  apply ext_inner_left ℝ
  intro w
  calc
    ⟪w, (normalizedYoungClebschRaise mu lam hdeg row c hc hgram).adjoint
        (v ⊗ₜ[ℝ] q)⟫_ℝ =
      ⟪normalizedYoungClebschRaise mu lam hdeg row c hc hgram w,
        v ⊗ₜ[ℝ] q⟫_ℝ :=
      LinearMap.adjoint_inner_right
        (normalizedYoungClebschRaise mu lam hdeg row c hc hgram).toLinearMap
        w (v ⊗ₜ[ℝ] q)
    _ = (Real.sqrt c)⁻¹ *
      ⟪youngClebschRaise mu lam hdeg row w, v ⊗ₜ[ℝ] q⟫_ℝ := by
      change
        ⟪((normalizedYoungClebschRaise mu lam hdeg row c hc hgram).toLinearMap)
          w, v ⊗ₜ[ℝ] q⟫_ℝ = _
      rw [normalizedYoungClebschRaise_toLinearMap,
        LinearMap.smul_apply, real_inner_smul_left]
    _ = (Real.sqrt c)⁻¹ *
      ⟪w, (youngClebschRaise mu lam hdeg row).adjoint
        (v ⊗ₜ[ℝ] q)⟫_ℝ := by
      rw [← LinearMap.adjoint_inner_right]
      rfl
    _ = (Real.sqrt c)⁻¹ *
      ⟪w, projectedCoordinateLower lam mu hdeg row v q⟫_ℝ := by
      rw [youngClebschRaise_adjoint_tmul]
    _ = ⟪w, (Real.sqrt c)⁻¹ •
        projectedCoordinateLower lam mu hdeg row v q⟫_ℝ :=
      (real_inner_smul_right _ _ _).symm

end FullRankClebschProbabilities

end

end HigherHarmonicYoung

namespace HigherChannel

section

open scoped BigOperators

/-- The raise weight used in the spherical-code argument. -/
def raiseWeight {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (ℓ : Fin (r + 1)) : Fin (r + 1) → ℕ :=
  Function.update lam ℓ (lam ℓ + 1)

@[simp] theorem ambientShift_raiseWeight_self {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (ℓ : Fin (r + 1)) :
    ambientShift n (raiseWeight lam ℓ) ℓ = ambientShift n lam ℓ + 1 := by
  simp only [ambientShift, raiseWeight, Function.update_self, Nat.cast_add, Nat.cast_one]
  ring

@[simp] theorem ambientShift_raiseWeight_other {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (ℓ j : Fin (r + 1)) (hj : j ≠ ℓ) :
    ambientShift n (raiseWeight lam ℓ) j = ambientShift n lam j := by
  simp only [ambientShift, raiseWeight, ne_eq, hj, not_false_eq_true, Function.update_of_ne]

/-- The weyl edge ratio used in the spherical-code argument. -/
def weylEdgeRatio {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (ℓ : Fin (r + 1)) : ℝ :=
  let L := ambientShift n lam ℓ
  let rho := wallShift n r
  ((L + 1) * (L + rho) / (L * (L + 1 - rho))) *
    ∏ q : Fin r,
      (((L + 1) ^ 2 - ambientShift n lam (ℓ.succAbove q) ^ 2) /
        (L ^ 2 - ambientShift n lam (ℓ.succAbove q) ^ 2))

theorem plusProbability_eq_weylEdgeRatio_mul_minus {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (ℓ : Fin (r + 1))
    (h : FiniteInterlacing n lam mu)
    (hraise : FiniteInterlacing n (raiseWeight lam ℓ) mu) :
    plusProbability n lam mu ℓ =
      weylEdgeRatio n lam ℓ *
        minusProbability n (raiseWeight lam ℓ) mu ℓ := by
  have hL : ambientShift n lam ℓ ≠ 0 := (h.ambientShift_pos ℓ).ne'
  have hLp : ambientShift n lam ℓ + 1 ≠ 0 := by
    linarith [h.ambientShift_pos ℓ]
  have hwall : ambientShift n lam ℓ + 1 - wallShift n r ≠ 0 := by
    have hle := h.wallShift_le_ambientShift ℓ
    linarith
  have hbase :
      (∏ q : Fin r,
        (ambientShift n lam ℓ ^ 2 -
          ambientShift n lam (ℓ.succAbove q) ^ 2)) ≠ 0 := by
    intro hz
    apply h.activeDenominator_ne_zero ℓ
    simp only [activeDenominator, hz, mul_zero]
  have htarget :
      (∏ q : Fin r,
        ((ambientShift n lam ℓ + 1) ^ 2 -
          ambientShift n lam (ℓ.succAbove q) ^ 2)) ≠ 0 := by
    intro hz
    apply hraise.activeDenominator_ne_zero ℓ
    unfold activeDenominator
    simp_rw [ambientShift_raiseWeight_self,
      ambientShift_raiseWeight_other lam ℓ _ (Fin.succAbove_ne ℓ _)]
    rw [hz]
    ring
  unfold plusProbability minusProbability weylEdgeRatio activeDenominator
  simp_rw [ambientShift_raiseWeight_self,
    ambientShift_raiseWeight_other lam ℓ _ (Fin.succAbove_ne ℓ _)]
  have hstabilizer :
      (∏ m : Fin r,
        ((ambientShift n lam ℓ + 1 - 1 / 2) ^ 2 -
          stabilizerShift n mu m ^ 2)) =
      ∏ m : Fin r,
        ((ambientShift n lam ℓ + 1 / 2) ^ 2 -
          stabilizerShift n mu m ^ 2) := by
    apply Finset.prod_congr rfl
    intro m _
    ring
  rw [hstabilizer, Finset.prod_div_distrib]
  field_simp [hL, hLp, hwall, hbase, htarget]

theorem FiniteInterlacing.antitone_ambient {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) : Antitone lam := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact (h.2 i).2.trans (h.2 i).1

private def pairEdgeRatio {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ j : Fin (r + 1)) : ℝ :=
  ((L ℓ + 1) ^ 2 - L j ^ 2) / (L ℓ ^ 2 - L j ^ 2)

theorem pairFactor_eq_shifted {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (i j : Fin (r + 1)) :
    HigherHierarchy.Weyl.pairFactor n lam i j =
      ((ambientShift n lam i - ambientShift n lam j) /
        ((j.val : ℝ) - (i.val : ℝ))) *
      ((ambientShift n lam i + ambientShift n lam j) /
        ((n : ℝ) - (i.val : ℝ) - (j.val : ℝ) - 2)) := by
  unfold HigherHierarchy.Weyl.pairFactor ambientShift
  congr 1 <;> congr 1 <;> ring

theorem pairFactor_raiseWeight {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (ℓ i j : Fin (r + 1)) (hij : i < j)
    (h : FiniteInterlacing n lam mu) :
    HigherHierarchy.Weyl.pairFactor n (raiseWeight lam ℓ) i j =
      HigherHierarchy.Weyl.pairFactor n lam i j *
        (if i = ℓ then pairEdgeRatio (ambientShift n lam) ℓ j
          else if j = ℓ then pairEdgeRatio (ambientShift n lam) ℓ i
          else 1) := by
  have hidx : (j.val : ℝ) - (i.val : ℝ) ≠ 0 := by
    have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
    linarith
  have hsum :=
    (HigherHierarchy.Weyl.sumDenominator_pos h.1 i j).ne'
  by_cases hi : i = ℓ
  · subst i
    have hj : j ≠ ℓ := ne_of_gt hij
    have hcoord :
        ambientShift n lam ℓ ^ 2 - ambientShift n lam j ^ 2 ≠ 0 := by
      have hlt := h.ambientShift_strictAnti hij
      nlinarith [h.ambientShift_pos ℓ, h.ambientShift_pos j]
    rw [pairFactor_eq_shifted, pairFactor_eq_shifted]
    simp only [ambientShift_raiseWeight_self, ambientShift_raiseWeight_other lam ℓ j hj, ↓reduceIte,
      pairEdgeRatio]
    field_simp [hidx, hsum, hcoord]
    ring
  · by_cases hj : j = ℓ
    · subst j
      have hcoord :
          ambientShift n lam ℓ ^ 2 - ambientShift n lam i ^ 2 ≠ 0 := by
        have hlt := h.ambientShift_strictAnti hij
        nlinarith [h.ambientShift_pos i, h.ambientShift_pos ℓ]
      rw [pairFactor_eq_shifted, pairFactor_eq_shifted]
      simp only [ambientShift_raiseWeight_other lam ℓ i hi, ambientShift_raiseWeight_self, hi,
        ↓reduceIte, pairEdgeRatio]
      field_simp [hidx, hsum, hcoord]
      ring
    · rw [pairFactor_eq_shifted, pairFactor_eq_shifted]
      simp only [ambientShift_raiseWeight_other lam ℓ i hi,
        ambientShift_raiseWeight_other lam ℓ j hj, hi, ↓reduceIte, hj, mul_one]

theorem incidentPairProduct {r : ℕ}
    (ℓ : Fin (r + 1)) (w : Fin (r + 1) → ℝ) :
    (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
      if i < j then
        (if i = ℓ then w j else if j = ℓ then w i else 1)
      else 1) =
        ∏ j ∈ Finset.univ.erase ℓ, w j := by
  classical
  let p : (Fin (r + 1) × Fin (r + 1)) → Prop :=
    fun z => z.1 < z.2 ∧ (z.1 = ℓ ∨ z.2 = ℓ)
  let other : (Fin (r + 1) × Fin (r + 1)) → Fin (r + 1) :=
    fun z => if z.1 = ℓ then z.2 else z.1
  have hrewrite :
      (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
        if i < j then
          (if i = ℓ then w j else if j = ℓ then w i else 1)
        else 1) =
      ∏ z ∈ (Finset.univ : Finset (Fin (r + 1) × Fin (r + 1))).filter p,
        w (other z) := by
    rw [Finset.prod_filter]
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro i _
    apply Finset.prod_congr rfl
    intro j _
    dsimp [p, other]
    by_cases hij : i < j <;> by_cases hi : i = ℓ <;>
      by_cases hj : j = ℓ <;> simp [hij, hi, hj]
  rw [hrewrite]
  symm
  refine Finset.prod_bij
    (fun j _ => if j < ℓ then (j, ℓ) else (ℓ, j))
    (fun j hj => ?_) (fun i hi j hj hij => ?_)
    (fun z hz => ?_) (fun j hj => ?_)
  · have hne : j ≠ ℓ := (Finset.mem_erase.mp hj).1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [p]
    split_ifs with hlt
    · exact ⟨hlt, Or.inr rfl⟩
    · exact ⟨lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne), Or.inl rfl⟩
  · have hi' : i ≠ ℓ := (Finset.mem_erase.mp hi).1
    have hj' : j ≠ ℓ := (Finset.mem_erase.mp hj).1
    split_ifs at hij with hil hjl
    · exact congrArg Prod.fst hij
    · exact False.elim (hi' (congrArg Prod.fst hij))
    · exact False.elim (hj' (congrArg Prod.fst hij).symm)
    · exact congrArg Prod.snd hij
  · rcases z with ⟨a, b⟩
    obtain ⟨hab, hside⟩ := (Finset.mem_filter.mp hz).2
    rcases hside with ha | hb
    · change a = ℓ at ha
      change a < b at hab
      subst a
      refine ⟨b, ?_, ?_⟩
      · simp only [Finset.mem_erase, ne_eq, ne_of_gt hab, not_false_eq_true, Finset.mem_univ,
          and_self]
      · have hnot : ¬b < ℓ := not_lt_of_ge hab.le
        simp only [hnot, ↓reduceIte]
    · change b = ℓ at hb
      change a < b at hab
      subst b
      refine ⟨a, ?_, ?_⟩
      · simp only [Finset.mem_erase, ne_eq, ne_of_lt hab, not_false_eq_true, Finset.mem_univ,
          and_self]
      · simp only [hab, ↓reduceIte]
  · dsimp [other]
    by_cases hlt : j < ℓ
    · simp only [hlt, ↓reduceIte, ne_of_lt hlt]
    · simp only [hlt, ↓reduceIte]

private def rowEdgeRatio {r : ℕ} (n : ℕ)
    (lam : Fin (r + 1) → ℕ) (ℓ : Fin (r + 1)) : ℝ :=
  let L := ambientShift n lam ℓ
  let rho := wallShift n r
  ((L + 1) * (L + rho)) / (L * (L + 1 - rho))

theorem tailLength_cast_eq_shifted {r n : ℕ}
    (hn : 2 * r + 4 ≤ n)
    (lam : Fin (r + 1) → ℕ) (ℓ : Fin (r + 1)) :
    (lam ℓ : ℝ) +
        (HigherHierarchy.Weyl.tailLength n r ℓ : ℝ) + 1 =
      ambientShift n lam ℓ + wallShift n r := by
  have hℓ : ℓ.val ≤ r := by omega
  have h₁ : ℓ.val ≤ n := by omega
  have h₂ : r ≤ n - ℓ.val := by omega
  have h₃ : 3 ≤ n - ℓ.val - r := by omega
  unfold HigherHierarchy.Weyl.tailLength ambientShift wallShift
  rw [Nat.cast_sub h₃, Nat.cast_sub h₂, Nat.cast_sub h₁]
  push_cast
  ring

theorem rowTail_cast_eq_shifted {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (ℓ : Fin (r + 1)) :
    (lam ℓ : ℝ) + (HigherHierarchy.Weyl.rowTail ℓ : ℝ) + 1 =
      ambientShift n lam ℓ + 1 - wallShift n r := by
  have hℓ : ℓ.val ≤ r := by omega
  unfold HigherHierarchy.Weyl.rowTail ambientShift wallShift
  rw [Nat.cast_sub hℓ]
  ring

theorem rowFactor_raiseWeight_self {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (ℓ : Fin (r + 1)) :
    HigherHierarchy.Weyl.rowFactor n (raiseWeight lam ℓ) ℓ =
      HigherHierarchy.Weyl.rowFactor n lam ℓ * rowEdgeRatio n lam ℓ := by
  have hrow :=
    HigherHierarchy.Weyl.rowFactor_update_succ_self h.1 lam ℓ
  change HigherHierarchy.Weyl.rowFactor n
    (Function.update lam ℓ (lam ℓ + 1)) ℓ = _
  rw [hrow]
  rw [tailLength_cast_eq_shifted h.1 lam ℓ,
    rowTail_cast_eq_shifted (n := n) lam ℓ]
  have hL : ambientShift n lam ℓ ≠ 0 :=
    (h.ambientShift_pos ℓ).ne'
  have hlin :
      2 * (lam ℓ : ℝ) + (n : ℝ) -
        2 * ((ℓ.val + 1 : ℕ) : ℝ) ≠ 0 := by
    push_cast
    intro hz
    apply hL
    unfold ambientShift
    linarith
  have hlinearRatio :
      (2 * (lam ℓ : ℝ) + (n : ℝ) -
        2 * ((ℓ.val + 1 : ℕ) : ℝ) + 2) /
        (2 * (lam ℓ : ℝ) + (n : ℝ) -
          2 * ((ℓ.val + 1 : ℕ) : ℝ)) =
        (ambientShift n lam ℓ + 1) / ambientShift n lam ℓ := by
    apply (div_eq_div_iff hlin hL).2
    unfold ambientShift
    push_cast
    ring
  rw [hlinearRatio]
  unfold rowEdgeRatio
  rw [mul_assoc, ← mul_div_mul_comm]

theorem rowFactor_raiseWeight_other {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (ℓ i : Fin (r + 1)) (hi : i ≠ ℓ) :
    HigherHierarchy.Weyl.rowFactor n (raiseWeight lam ℓ) i =
      HigherHierarchy.Weyl.rowFactor n lam i := by
  exact HigherHierarchy.Weyl.rowFactor_update_succ_ne n lam ℓ i hi

theorem rowFactorProduct_raiseWeight {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (h : FiniteInterlacing n lam mu) (ℓ : Fin (r + 1)) :
    (∏ i : Fin (r + 1),
      HigherHierarchy.Weyl.rowFactor n (raiseWeight lam ℓ) i) =
      (∏ i : Fin (r + 1), HigherHierarchy.Weyl.rowFactor n lam i) *
        rowEdgeRatio n lam ℓ := by
  classical
  calc
    (∏ i : Fin (r + 1),
      HigherHierarchy.Weyl.rowFactor n (raiseWeight lam ℓ) i) =
      ∏ i : Fin (r + 1),
        (HigherHierarchy.Weyl.rowFactor n lam i *
          if i = ℓ then rowEdgeRatio n lam ℓ else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i = ℓ
        · subst i
          simp only [rowFactor_raiseWeight_self h ℓ, ↓reduceIte]
        · simp only [rowFactor_raiseWeight_other lam ℓ i hi, hi, ↓reduceIte, mul_one]
    _ = (∏ i : Fin (r + 1), HigherHierarchy.Weyl.rowFactor n lam i) *
          ∏ i : Fin (r + 1), if i = ℓ then rowEdgeRatio n lam ℓ else 1 := by
        rw [Finset.prod_mul_distrib]
    _ = (∏ i : Fin (r + 1), HigherHierarchy.Weyl.rowFactor n lam i) *
          rowEdgeRatio n lam ℓ := by simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem pairEdgeRatio_prod_erase_eq {r : ℕ}
    (L : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    (∏ j ∈ Finset.univ.erase ℓ, pairEdgeRatio L ℓ j) =
      ∏ q : Fin r, pairEdgeRatio L ℓ (ℓ.succAbove q) := by
  classical
  symm
  refine Finset.prod_bij (fun j _ => ℓ.succAbove j)
    (fun j _ => ?_) (fun i _ j _ hij => ?_) (fun j hj => ?_)
    (fun _ _ => rfl)
  · simp only [Finset.mem_erase, ne_eq, Fin.succAbove_ne, not_false_eq_true, Finset.mem_univ,
      and_self]
  · exact Fin.succAbove_right_injective hij
  · obtain ⟨hj', _⟩ := Finset.mem_erase.mp hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj'
    exact ⟨i, Finset.mem_univ i, hi⟩

theorem pairFactorProduct_raiseWeight {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (ℓ : Fin (r + 1))
    (h : FiniteInterlacing n lam mu) :
    (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
      if i < j then
        HigherHierarchy.Weyl.pairFactor n (raiseWeight lam ℓ) i j
      else 1) =
      (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
        if i < j then HigherHierarchy.Weyl.pairFactor n lam i j else 1) *
      ∏ q : Fin r,
        pairEdgeRatio (ambientShift n lam) ℓ (ℓ.succAbove q) := by
  classical
  calc
    (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
      if i < j then
        HigherHierarchy.Weyl.pairFactor n (raiseWeight lam ℓ) i j
      else 1) =
      ∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
        ((if i < j then HigherHierarchy.Weyl.pairFactor n lam i j else 1) *
          (if i < j then
            (if i = ℓ then pairEdgeRatio (ambientShift n lam) ℓ j
              else if j = ℓ then pairEdgeRatio (ambientShift n lam) ℓ i
              else 1)
          else 1)) := by
        apply Finset.prod_congr rfl
        intro i _
        apply Finset.prod_congr rfl
        intro j _
        by_cases hij : i < j
        · simp only [ite_eq_left hij]
          exact pairFactor_raiseWeight ℓ i j hij h
        · simp only [hij, ↓reduceIte, mul_one]
    _ = (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
          if i < j then HigherHierarchy.Weyl.pairFactor n lam i j else 1) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
          if i < j then
            (if i = ℓ then pairEdgeRatio (ambientShift n lam) ℓ j
              else if j = ℓ then pairEdgeRatio (ambientShift n lam) ℓ i
              else 1)
          else 1) := by
        simp_rw [Finset.prod_mul_distrib]
    _ = (∏ i : Fin (r + 1), ∏ j : Fin (r + 1),
          if i < j then HigherHierarchy.Weyl.pairFactor n lam i j else 1) *
        ∏ j ∈ Finset.univ.erase ℓ,
          pairEdgeRatio (ambientShift n lam) ℓ j := by
        rw [incidentPairProduct]
    _ = _ := by rw [pairEdgeRatio_prod_erase_eq]

theorem weylDimension_raiseWeight {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (ℓ : Fin (r + 1))
    (h : FiniteInterlacing n lam mu) :
    HigherHierarchy.Weyl.dimension n (raiseWeight lam ℓ) =
      HigherHierarchy.Weyl.dimension n lam * weylEdgeRatio n lam ℓ := by
  unfold HigherHierarchy.Weyl.dimension
  rw [rowFactorProduct_raiseWeight h ℓ,
    pairFactorProduct_raiseWeight ℓ h]
  unfold weylEdgeRatio rowEdgeRatio pairEdgeRatio
  ring

theorem actual_weyl_detailed_balance {r n : ℕ}
    {lam : Fin (r + 1) → ℕ} {mu : Fin r → ℕ}
    (ℓ : Fin (r + 1))
    (h : FiniteInterlacing n lam mu)
    (hraise : FiniteInterlacing n (raiseWeight lam ℓ) mu) :
    HigherHierarchy.Weyl.dimension n lam * plusProbability n lam mu ℓ =
      HigherHierarchy.Weyl.dimension n (raiseWeight lam ℓ) *
        minusProbability n (raiseWeight lam ℓ) mu ℓ := by
  rw [plusProbability_eq_weylEdgeRatio_mul_minus ℓ h hraise,
    weylDimension_raiseWeight ℓ h]
  ring

end

section


open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy

/-- The floored coordinates used in the spherical-code argument. -/
def flooredCoordinates {I : Type*} (a : I → ℝ) (n : ℕ) : I → ℕ :=
  fun i => ⌊a i * (n : ℝ)⌋₊

theorem tendsto_flooredCoordinates_ratio {I : Type*}
    (a : I → ℝ) (i : I) (ha : 0 ≤ a i) :
    Tendsto
      (fun n : ℕ => (flooredCoordinates a n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)) := by
  simpa only [flooredCoordinates, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_wallShift_div (r : ℕ) :
    Tendsto (fun n : ℕ => wallShift n r / (n : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hdimension := SpherePacking.tendsto_natCast_div_self
  have hrow := tendsto_const_div_atTop_nhds_zero_nat ((r : ℝ) + 1)
  convert (hdimension.div_const (2 : ℝ)).sub hrow using 1
  · ext n
    simp only [wallShift, div_eq_mul_inv]
    ring
  · ring_nf

end

end HigherChannel

section


open Filter Topology
open scoped BigOperators Matrix Topology

namespace HigherHierarchyBoxSpectral

open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherChannel

/-- The box vertex used in the spherical-code argument. -/
abbrev BoxVertex (r m : ℕ) := Fin (r + 1) → Fin (m + 1)

/-- The next vertex used in the spherical-code argument. -/
def nextVertex {r m : ℕ} (v : BoxVertex r m)
    (i : Fin (r + 1)) (h : (v i).val < m) : BoxVertex r m :=
  Function.update v i ⟨(v i).val + 1, by omega⟩

private def forwardMatrix {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    Matrix (BoxVertex r m) (BoxVertex r m) ℝ :=
  Matrix.of fun v w =>
    ∑ i : Fin (r + 1),
      if h : (v i).val < m then
        if w = nextVertex v i h then edge v i else 0
      else 0

private def adjacencyMatrix {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    Matrix (BoxVertex r m) (BoxVertex r m) ℝ :=
  forwardMatrix edge + (forwardMatrix edge)ᵀ

theorem adjacencyMatrix_transpose {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    (adjacencyMatrix edge)ᵀ = adjacencyMatrix edge := by
  simp only [adjacencyMatrix, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

theorem boxVertex_card (r m : ℕ) :
    Fintype.card (BoxVertex r m) = (m + 1) ^ (r + 1) := by
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]

theorem upperFace_card {r m : ℕ} (i : Fin (r + 1)) :
    ((Finset.univ : Finset (BoxVertex r m)).filter
      (fun v => v i = Fin.last m)).card = (m + 1) ^ r := by
  classical
  simpa only [Fintype.piFinset_univ, Finset.card_univ, Fintype.card_fin, add_tsub_cancel_right]
    using
    (Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset (Fin (m + 1))) i
      (Finset.mem_univ (Fin.last m)))

theorem forwardFace_card {r m : ℕ} (i : Fin (r + 1)) :
    ((Finset.univ : Finset (BoxVertex r m)).filter
      (fun v => (v i).val < m)).card = m * (m + 1) ^ r := by
  classical
  have hcomplement :
      ((Finset.univ : Finset (BoxVertex r m)).filter
        (fun v => v i = Fin.last m)).card +
        ((Finset.univ : Finset (BoxVertex r m)).filter
          (fun v => ¬ v i = Fin.last m)).card =
          (Finset.univ : Finset (BoxVertex r m)).card :=
    Finset.card_filter_add_card_filter_not _
  have hfilter :
      (Finset.univ : Finset (BoxVertex r m)).filter
          (fun v => ¬ v i = Fin.last m) =
        (Finset.univ : Finset (BoxVertex r m)).filter
          (fun v => (v i).val < m) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hne
      have hle := (v i).isLt
      have hval : (v i).val ≠ m := by
        intro heq
        exact hne (Fin.ext heq)
      omega
    · intro hlt heq
      have hval := congrArg Fin.val heq
      simp only [Fin.val_last] at hval
      omega
  rw [upperFace_card, hfilter] at hcomplement
  have hfull :
      (Finset.univ : Finset (BoxVertex r m)).card =
        (m + 1) ^ (r + 1) := boxVertex_card r m
  rw [hfull] at hcomplement
  have hfactor :
      (m + 1) ^ (r + 1) =
        (m + 1) ^ r + m * (m + 1) ^ r := by
    rw [pow_succ]
    ring
  omega

theorem forwardMatrix_sum {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    (∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
      forwardMatrix edge v w) =
      ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
        if (v i).val < m then edge v i else 0 := by
  classical
  unfold forwardMatrix
  simp only [Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : (v i).val < m
  · simp only [h, ↓reduceDIte, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · simp only [h, ↓reduceDIte, Finset.sum_const_zero, ↓reduceIte]

theorem adjacencyMatrix_sum {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    (∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
      adjacencyMatrix edge v w) =
      2 * ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
        if (v i).val < m then edge v i else 0 := by
  classical
  have htranspose :
      (∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
        (forwardMatrix edge)ᵀ v w) =
        ∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
          forwardMatrix edge v w := by
    simp only [Matrix.transpose_apply]
    exact Finset.sum_comm
  simp_rw [adjacencyMatrix, Matrix.add_apply]
  simp_rw [Finset.sum_add_distrib]
  rw [htranspose, forwardMatrix_sum]
  ring

private def constantRayleigh {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) : ℝ :=
  (∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
    adjacencyMatrix edge v w) /
      (Fintype.card (BoxVertex r m) : ℝ)

theorem constantRayleigh_eq {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    constantRayleigh edge =
      (2 * ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
        if (v i).val < m then edge v i else 0) /
          (Fintype.card (BoxVertex r m) : ℝ) := by
  rw [constantRayleigh, adjacencyMatrix_sum]

theorem forwardFace_sum {r m : ℕ}
    (i : Fin (r + 1)) (c : ℝ) :
    (∑ v : BoxVertex r m,
      if (v i).val < m then c else 0) =
        (m : ℝ) * ((m + 1 : ℕ) : ℝ) ^ r * c := by
  classical
  have hterm (v : BoxVertex r m) :
      (if (v i).val < m then c else 0) =
        (if (v i).val < m then (1 : ℝ) else 0) * c := by
    split_ifs <;> simp
  simp_rw [hterm, ← Finset.sum_mul]
  rw [Finset.sum_boole]
  rw [forwardFace_card]
  norm_cast

theorem constantRayleigh_const {r m : ℕ}
    (weight : Fin (r + 1) → ℝ) :
    constantRayleigh (fun _ : BoxVertex r m => weight) =
      (2 * (m : ℝ) / (m + 1 : ℝ)) *
        ∑ i : Fin (r + 1), weight i := by
  rw [constantRayleigh_eq, boxVertex_card]
  rw [Finset.sum_comm]
  simp_rw [forwardFace_sum]
  rw [← Finset.mul_sum]
  push_cast
  have hbase : (m : ℝ) + 1 ≠ 0 := by positivity
  have hpower : ((m : ℝ) + 1) ^ r ≠ 0 :=
    pow_ne_zero _ hbase
  rw [pow_succ]
  field_simp

theorem constantRayleigh_tendsto {r m : ℕ}
    (edge : ℕ → BoxVertex r m → Fin (r + 1) → ℝ)
    (weight : Fin (r + 1) → ℝ)
    (hlimit : ∀ (v : BoxVertex r m) (i : Fin (r + 1)),
      Tendsto (fun n : ℕ => edge n v i) atTop (𝓝 (weight i))) :
    Tendsto (fun n : ℕ => constantRayleigh (edge n))
      atTop
      (𝓝 ((2 * (m : ℝ) / (m + 1 : ℝ)) *
        ∑ i : Fin (r + 1), weight i)) := by
  classical
  have hsum :
      Tendsto
        (fun n : ℕ =>
          ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
            if (v i).val < m then edge n v i else 0)
        atTop
        (𝓝 (∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
          if (v i).val < m then weight i else 0)) := by
    apply tendsto_finsetSum
    intro v _
    apply tendsto_finsetSum
    intro i _
    by_cases h : (v i).val < m
    · simpa only [h, ↓reduceIte] using hlimit v i
    · simp only [h, ↓reduceIte, tendsto_const_nhds_iff]
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hquotient :
      Tendsto
        (fun n : ℕ =>
          (2 * (∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
            if (v i).val < m then edge n v i else 0)) /
              (Fintype.card (BoxVertex r m) : ℝ))
        atTop
        (𝓝 ((2 * (∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
          if (v i).val < m then weight i else 0)) /
            (Fintype.card (BoxVertex r m) : ℝ))) :=
    (htwo.mul hsum).div_const
      (Fintype.card (BoxVertex r m) : ℝ)
  have hresult :
      Tendsto (fun n : ℕ => constantRayleigh (edge n)) atTop
        (𝓝 (constantRayleigh (fun _ : BoxVertex r m => weight))) := by
    simpa only [constantRayleigh_eq] using hquotient
  rw [constantRayleigh_const] at hresult
  exact hresult

end HigherHierarchyBoxSpectral

end

section


open Filter Topology
open scoped BigOperators Topology

namespace HigherHierarchy.RectangularVertices

open MetricCodes.Spherical.HigherChannel

/-- The vertex used in the spherical-code argument. -/
abbrev Vertex (r m : ℕ) := Fin (r + 1) → Fin (m + 1)

/-- The signature used in the spherical-code argument. -/
def signature {r : ℕ} (a : Fin (r + 1) → ℝ)
    (n : ℕ) {m : ℕ} (v : Vertex r m) : Fin (r + 1) → ℕ :=
  fun i => flooredCoordinates a n i + (v i).val

theorem tendsto_offset_div {r m : ℕ}
    (v : ℕ → Vertex r m) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => ((v n i).val : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact_mod_cast (show (v n i).val ≤ m by omega)

theorem tendsto_signature_ratio {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (v : ℕ → Vertex r m)
    (i : Fin (r + 1)) (ha : 0 ≤ a i) :
    Tendsto (fun n : ℕ => (signature a n (v n) i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)) := by
  have hfloor := tendsto_flooredCoordinates_ratio a i ha
  have hoffset := tendsto_offset_div v i
  convert hfloor.add hoffset using 1
  · ext n
    simp only [signature, Nat.cast_add, add_div]
  · simp only [add_zero]

theorem eventually_signature_lt_of_lt {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (v : ℕ → Vertex r m)
    (i j : Fin (r + 1)) (hi : 0 ≤ a i) (hj : 0 ≤ a j)
    (hij : a i < a j) :
    ∀ᶠ n : ℕ in atTop, signature a n (v n) i < signature a n (v n) j := by
  have hratio :=
    ((tendsto_signature_ratio a v j hj).sub
      (tendsto_signature_ratio a v i hi)).eventually
        (Ioi_mem_nhds (sub_pos.mpr hij))
  filter_upwards [hratio, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hcast :
      (signature a n (v n) i : ℝ) < signature a n (v n) j := by
    apply (div_lt_div_iff_of_pos_right hnreal).mp
    linarith
  exact_mod_cast hcast

theorem eventually_signature_strictAnti {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) :
    ∀ᶠ n : ℕ in atTop, StrictAnti (signature a n (v n)) := by
  have hall :
      ∀ᶠ n : ℕ in atTop, ∀ i : Fin r,
        signature a n (v n) i.succ <
          signature a n (v n) i.castSucc := by
    apply eventually_all.2
    intro i
    exact eventually_signature_lt_of_lt a v i.succ i.castSucc
      (ha i.succ) (ha i.castSucc)
      (hanti (show i.castSucc < i.succ from Fin.castSucc_lt_succ))
  filter_upwards [hall] with n hn
  exact Fin.strictAnti_iff_succ_lt.mpr hn

theorem eventually_strictInterlaces_all {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
      HigherRepresentationGraph.StrictInterlaces
        (signature a n v) (flooredCoordinates b n) := by
  apply eventually_all.2
  intro v
  apply eventually_all.2
  intro i
  let V : ℕ → Vertex r m := fun _ => v
  have hab :=
    ((tendsto_signature_ratio a V i.castSucc
      (h.ambient_nonneg i.castSucc)).sub
      (tendsto_flooredCoordinates_ratio b i
        (h.stabilizer_pos i).le)).eventually
          (Ioi_mem_nhds (sub_pos.mpr (h.2 i).1))
  have hba :=
    ((tendsto_flooredCoordinates_ratio b i
      (h.stabilizer_pos i).le).sub
      (tendsto_signature_ratio a V i.succ
        (h.ambient_nonneg i.succ))).eventually
          (Ioi_mem_nhds (sub_pos.mpr (h.2 i).2))
  filter_upwards [hab, hba, eventually_gt_atTop (0 : ℕ)] with n hn hn' hnpos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  constructor
  · exact_mod_cast
      ((div_lt_div_iff_of_pos_right hnreal).mp
        (show (flooredCoordinates b n i : ℝ) / n <
          (signature a n v i.castSucc : ℝ) / n by
            change 0 < _ at hn
            dsimp [V] at hn
            linarith))
  · exact_mod_cast
      ((div_lt_div_iff_of_pos_right hnreal).mp
        (show (signature a n v i.succ : ℝ) / n <
          (flooredCoordinates b n i : ℝ) / n by
            change 0 < _ at hn'
            dsimp [V] at hn'
            linarith))

theorem eventually_finiteInterlacing_all {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
      FiniteInterlacing n (signature a n v) (flooredCoordinates b n) := by
  filter_upwards [eventually_strictInterlaces_all (m := m) a b h,
    eventually_ge_atTop (2 * r + 4)] with n hn hstable
  intro v
  exact ⟨hstable, (hn v).interlaces⟩

private def correctedSignature {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (v : ℕ → Vertex r m)
    (n : ℕ) : Fin (r + 1) → ℕ :=
  if Antitone (signature a n (v n)) then
    signature a n (v n)
  else
    Weyl.flooredWeight a n

theorem correctedSignature_antitone {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (hanti : Antitone a)
    (v : ℕ → Vertex r m) (n : ℕ) :
    Antitone (correctedSignature a v n) := by
  classical
  unfold correctedSignature
  split_ifs with h
  · exact h
  · exact Weyl.flooredWeight_antitone hanti n

theorem eventually_correctedSignature_eq {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) :
    ∀ᶠ n : ℕ in atTop,
      correctedSignature a v n = signature a n (v n) := by
  filter_upwards [eventually_signature_strictAnti a ha hanti v]
    with n hn
  simp only [correctedSignature, hn.antitone, ↓reduceIte]

theorem tendsto_correctedSignature_ratio {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) (i : Fin (r + 1)) :
    Tendsto
      (fun n : ℕ => (correctedSignature a v n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)) := by
  apply (tendsto_signature_ratio a v i (ha i)).congr'
  filter_upwards [eventually_correctedSignature_eq a ha hanti v]
    with n hn
  rw [hn]

theorem tendsto_correctedSignature_atTop {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => correctedSignature a v n i) atTop atTop := by
  have hfloor :
      Tendsto (fun n : ℕ => flooredCoordinates a n i) atTop atTop := by
    exact tendsto_nat_floor_mul_atTop (a i) (ha i)
  apply tendsto_atTop_mono' atTop _ hfloor
  filter_upwards [eventually_correctedSignature_eq a
    (fun j => (ha j).le) hanti v] with n hn
  rw [hn]
  exact Nat.le_add_right _ _

theorem tendsto_log_vertexDimension_div_log_two {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (Weyl.dimension n (signature a n (v n))) /
          (n : ℝ)) / Real.log 2)
      atTop
      (𝓝 (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))) := by
  have hcorrected := Weyl.tendsto_log_dimension_div_log_two
    (correctedSignature a v) a ha hanti
    (correctedSignature_antitone a hanti.antitone v)
    (tendsto_correctedSignature_atTop a ha hanti v)
    (tendsto_correctedSignature_ratio a (fun i => (ha i).le) hanti v)
  apply hcorrected.congr'
  filter_upwards [eventually_correctedSignature_eq a
    (fun i => (ha i).le) hanti v] with n hn
  rw [hn]

/-- The vertex dimension used in the spherical-code argument. -/
def vertexDimension {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (n : ℕ) (v : Vertex r m) : ℝ :=
  Weyl.dimension n (signature a n v)

/-- The dimension sum used in the spherical-code argument. -/
def dimensionSum {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (n : ℕ) : ℝ :=
  ∑ v : Vertex r m, vertexDimension a n v

theorem eventually_vertexDimension_pos_all {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
      0 < vertexDimension a n v := by
  have hdominant :
      ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
        StrictAnti (signature a n v) := by
    apply eventually_all.2
    intro v
    exact eventually_signature_strictAnti a
      (fun i => (ha i).le) hanti (fun _ => v)
  filter_upwards [hdominant, eventually_ge_atTop (2 * r + 4)]
    with n hn hstable v
  exact Weyl.dimension_pos hstable (hn v).antitone

theorem tendsto_log_finset_sum
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (H : ℝ)
    (hf : ∀ i n, 0 < f i n)
    (hlim : ∀ i, Tendsto (fun n : ℕ => Real.log (f i n) / (n : ℝ))
      atTop (𝓝 H)) :
    Tendsto (fun n : ℕ => Real.log (∑ i, f i n) / (n : ℝ))
      atTop (𝓝 H) := by
  classical
  let s : Finset ι := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  let M : ℕ → ℝ := fun n =>
    s.sup' hs (fun i => Real.log (f i n) / (n : ℝ))
  have hM : Tendsto M atTop (𝓝 H) := by
    simpa only [Finset.sup'_const] using (Filter.Tendsto.finset_sup'_nhds_apply hs (fun i (_ : i
      ∈ s) => hlim i))
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast hs.card_pos
  have herr : Tendsto
      (fun n : ℕ => Real.log (s.card : ℝ) / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have hupper : Tendsto
      (fun n : ℕ => M n + Real.log (s.card : ℝ) / (n : ℝ))
      atTop (𝓝 H) := by
    simpa only [add_zero] using hM.add herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hM hupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    apply Finset.sup'_le hs _
    intro i hi
    apply div_le_div_of_nonneg_right _ hnreal.le
    apply Real.log_le_log (hf i n)
    exact Finset.single_le_sum (fun j _ => (hf j n).le) hi
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hbound : ∀ i ∈ s, f i n ≤ Real.exp ((n : ℝ) * M n) := by
      intro i hi
      apply Real.le_exp_of_log_le
      have hsup : Real.log (f i n) / (n : ℝ) ≤ M n := by
        exact Finset.le_sup' (fun i => Real.log (f i n) / (n : ℝ)) hi
      simpa only [ge_iff_le, mul_comm] using (div_le_iff₀ hnreal).mp hsup
    have hsum :
        (∑ i ∈ s, f i n) ≤
          (s.card : ℝ) * Real.exp ((n : ℝ) * M n) := by
      simpa only [nsmul_eq_mul] using (s.sum_le_card_nsmul (fun i => f i n) (Real.exp ((n : ℝ) *
        M n)) hbound)
    have hsumpos : 0 < ∑ i ∈ s, f i n := by
      exact Finset.sum_pos (fun i _ => hf i n) hs
    have hlog := Real.log_le_log hsumpos hsum
    rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    change Real.log (∑ i ∈ s, f i n) / (n : ℝ) ≤ _
    apply (div_le_iff₀ hnreal).2
    calc
      Real.log (∑ i ∈ s, f i n) ≤
          Real.log (s.card : ℝ) + (n : ℝ) * M n := hlog
      _ = (M n + Real.log (s.card : ℝ) / (n : ℝ)) * (n : ℝ) := by
        field_simp
        ring

theorem tendsto_log_finset_sum_of_eventually_pos
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (H : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, ∀ i, 0 < f i n)
    (hlim : ∀ i, Tendsto (fun n : ℕ => Real.log (f i n) / (n : ℝ))
      atTop (𝓝 H)) :
    Tendsto (fun n : ℕ => Real.log (∑ i, f i n) / (n : ℝ))
      atTop (𝓝 H) := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hf)
  let g : ι → ℕ → ℝ := fun i n => if N ≤ n then f i n else 1
  have hg : ∀ i n, 0 < g i n := by
    intro i n
    dsimp [g]
    split_ifs with hn
    · exact hN n hn i
    · norm_num
  have hgeq : ∀ i, (fun n => g i n) =ᶠ[atTop] (fun n => f i n) := by
    intro i
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [hn, ↓reduceIte, g]
  have hglim : ∀ i, Tendsto
      (fun n : ℕ => Real.log (g i n) / (n : ℝ)) atTop (𝓝 H) := by
    intro i
    apply (hlim i).congr'
    filter_upwards [hgeq i] with n hn
    rw [hn]
  have hsum := tendsto_log_finset_sum g H hg hglim
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [hn, ↓reduceIte, g]

theorem tendsto_log_finset_sum_div_log_two_of_eventually_pos
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ → ℝ) (H : ℝ)
    (hf : ∀ᶠ n : ℕ in atTop, ∀ i, 0 < f i n)
    (hlim : ∀ i, Tendsto
      (fun n : ℕ => (Real.log (f i n) / (n : ℝ)) / Real.log 2)
      atTop (𝓝 H)) :
    Tendsto
      (fun n : ℕ => (Real.log (∑ i, f i n) / (n : ℝ)) / Real.log 2)
      atTop (𝓝 H) := by
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hlim' : ∀ i, Tendsto
      (fun n : ℕ => Real.log (f i n) / (n : ℝ))
      atTop (𝓝 (H * Real.log 2)) := by
    intro i
    have h := (hlim i).mul_const (Real.log 2)
    simpa only [isUnit_iff_ne_zero, ne_eq, hlog, not_false_eq_true, IsUnit.div_mul_cancel] using h
  have hsum := tendsto_log_finset_sum_of_eventually_pos
    f (H * Real.log 2) hf hlim'
  have h := hsum.div_const (Real.log 2)
  simpa only [isUnit_iff_ne_zero, ne_eq, hlog, not_false_eq_true,
    IsUnit.mul_div_cancel_right] using h

theorem tendsto_log_dimensionSum_div_log_two {r m : ℕ}
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (dimensionSum (m := m) a n) / (n : ℝ)) / Real.log 2)
      atTop
      (𝓝 (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))) := by
  apply tendsto_log_finset_sum_div_log_two_of_eventually_pos
    (fun v n => vertexDimension a n v)
    (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (a i))
    (eventually_vertexDimension_pos_all a ha hanti)
  intro v
  exact tendsto_log_vertexDimension_div_log_two a ha hanti (fun _ => v)

/-- The next vertex used in the spherical-code argument. -/
def nextVertex {r m : ℕ} (v : Vertex r m)
    (i : Fin (r + 1)) (h : (v i).val < m) : Vertex r m :=
  Function.update v i ⟨(v i).val + 1, by omega⟩

theorem signature_nextVertex {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (n : ℕ) (v : Vertex r m)
    (i : Fin (r + 1)) (h : (v i).val < m) :
    signature a n (nextVertex v i h) =
      raiseWeight (signature a n v) i := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [signature, nextVertex, Function.update_self, raiseWeight]
    omega
  · simp only [signature, nextVertex, ne_eq, hj, not_false_eq_true, Function.update_of_ne,
      raiseWeight]

theorem tendsto_ambientShift_of_ratio {r : ℕ}
    (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1))
    (hlim : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i))) :
    Tendsto (fun n : ℕ => ambientShift n (lam n) i / (n : ℝ))
      atTop (𝓝 (a i + (1 / 2 : ℝ))) := by
  have hdimension := SpherePacking.tendsto_natCast_div_self
  have hrow :=
    tendsto_const_div_atTop_nhds_zero_nat ((i.val : ℝ) + 1)
  convert (hlim.add (hdimension.div_const (2 : ℝ))).sub hrow using 1
  · ext n
    simp only [ambientShift, div_eq_mul_inv]
    ring
  · ring_nf

theorem tendsto_stabilizerShift_of_ratio {r : ℕ}
    (mu : ℕ → Fin r → ℕ)
    (b : Fin r → ℝ) (i : Fin r)
    (hlim : Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i))) :
    Tendsto (fun n : ℕ => stabilizerShift n (mu n) i / (n : ℝ))
      atTop (𝓝 (b i + (1 / 2 : ℝ))) := by
  have hdimension := SpherePacking.tendsto_natCast_div_self
  have hone := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hrow :=
    tendsto_const_div_atTop_nhds_zero_nat ((i.val : ℝ) + 1)
  convert
    (hlim.add ((hdimension.sub hone).div_const (2 : ℝ))).sub hrow
      using 1
  · ext n
    simp only [stabilizerShift, div_eq_mul_inv]
    ring
  · ring_nf

theorem tendsto_channelFactor_of_ratios {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (lam : ℕ → Fin (r + 1) → ℕ) (mu : ℕ → Fin r → ℕ)
    (hlam : ∀ i, Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)))
    (hmu : ∀ i, Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i)))
    (i : Fin (r + 1)) (j : Fin r) (c d : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (((ambientShift n (lam n) i + c) ^ 2 -
          stabilizerShift n (mu n) j ^ 2) /
          ((ambientShift n (lam n) i + d) ^ 2 -
            ambientShift n (lam n) (i.succAbove j) ^ 2)))
      atTop
      (𝓝 ((((a i) * (1 + (a i))) - ((b j) * (1 + (b j)))) /
        (((a i) * (1 + (a i))) -
          ((a (i.succAbove j)) * (1 + (a (i.succAbove j))))))) := by
  have hai := tendsto_ambientShift_of_ratio lam a i (hlam i)
  have haj := tendsto_ambientShift_of_ratio lam a
    (i.succAbove j) (hlam (i.succAbove j))
  have hbj := tendsto_stabilizerShift_of_ratio mu b j (hmu j)
  have hc := tendsto_const_div_atTop_nhds_zero_nat c
  have hd := tendsto_const_div_atTop_nhds_zero_nat d
  have hnum := (hai.add hc).pow 2 |>.sub (hbj.pow 2)
  have hden := (hai.add hd).pow 2 |>.sub (haj.pow 2)
  have hne :
      ((a i) * (1 + (a i))) -
        ((a (i.succAbove j)) * (1 + (a (i.succAbove j)))) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact Fin.ne_succAbove i j (h.quadratic_injective heq)
  have hnum' : Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i / (n : ℝ) + c / (n : ℝ)) ^ 2 -
          (stabilizerShift n (mu n) j / (n : ℝ)) ^ 2)
      atTop
      (𝓝 (((a i) * (1 + (a i))) - ((b j) * (1 + (b j))))) := by
    convert hnum using 1
    ring_nf
  have hden' : Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i / (n : ℝ) + d / (n : ℝ)) ^ 2 -
          (ambientShift n (lam n) (i.succAbove j) / (n : ℝ)) ^ 2)
      atTop
      (𝓝 (((a i) * (1 + (a i))) -
        ((a (i.succAbove j)) * (1 + (a (i.succAbove j)))))) := by
    convert hden using 1
    ring_nf
  have hlimit : Tendsto
      (fun n : ℕ =>
        (((ambientShift n (lam n) i / (n : ℝ) + c / (n : ℝ)) ^ 2 -
          (stabilizerShift n (mu n) j / (n : ℝ)) ^ 2) /
          ((ambientShift n (lam n) i / (n : ℝ) + d / (n : ℝ)) ^ 2 -
            (ambientShift n (lam n) (i.succAbove j) / (n : ℝ)) ^ 2)))
      atTop
      (𝓝 ((((a i) * (1 + (a i))) - ((b j) * (1 + (b j)))) /
        (((a i) * (1 + (a i))) -
          ((a (i.succAbove j)) * (1 + (a (i.succAbove j))))))) := by
    exact hnum'.div hden' hne
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn']

theorem tendsto_plusLeadingFactor_of_ratio {r : ℕ}
    (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1)) (ha : 0 ≤ a i)
    (hlim : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i + wallShift n r) /
          (2 * ambientShift n (lam n) i))
      atTop (𝓝 ((a i + 1) / (2 * a i + 1))) := by
  have hambient := tendsto_ambientShift_of_ratio lam a i hlim
  have hwall := tendsto_wallShift_div r
  have hden : 2 * (a i + (1 / 2 : ℝ)) ≠ 0 := by positivity
  have hlimit :=
    (hambient.add hwall).div (hambient.const_mul (2 : ℝ)) hden
  have hconverted :
      Tendsto
        (fun n : ℕ =>
          (ambientShift n (lam n) i / (n : ℝ) +
            wallShift n r / (n : ℝ)) /
            (2 * (ambientShift n (lam n) i / (n : ℝ))))
        atTop (𝓝 ((a i + 1) / (2 * a i + 1))) := by
    convert hlimit using 1
    · funext n
      rfl
    · congr 1
      ring
  apply hconverted.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn']

theorem tendsto_raisedMinusLeadingFactor_of_ratio {r : ℕ}
    (lam : ℕ → Fin (r + 1) → ℕ)
    (a : Fin (r + 1) → ℝ) (i : Fin (r + 1)) (ha : 0 ≤ a i)
    (hlim : Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i))) :
    Tendsto
      (fun n : ℕ =>
        (ambientShift n (lam n) i + 1 - wallShift n r) /
          (2 * (ambientShift n (lam n) i + 1)))
      atTop (𝓝 (a i / (2 * a i + 1))) := by
  have hambient := tendsto_ambientShift_of_ratio lam a i hlim
  have hone := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hshift := hambient.add hone
  have hwall := tendsto_wallShift_div r
  have hden : 2 * (a i + (1 / 2 : ℝ) + 0) ≠ 0 := by positivity
  have hlimit :=
    (hshift.sub hwall).div (hshift.const_mul (2 : ℝ)) hden
  have hconverted :
      Tendsto
        (fun n : ℕ =>
          (ambientShift n (lam n) i / (n : ℝ) +
              (1 : ℝ) / (n : ℝ) - wallShift n r / (n : ℝ)) /
            (2 * (ambientShift n (lam n) i / (n : ℝ) +
              (1 : ℝ) / (n : ℝ))))
        atTop (𝓝 (a i / (2 * a i + 1))) := by
    convert hlimit using 1
    · funext n
      rfl
    · congr 1
      ring
  apply hconverted.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn']

theorem tendsto_plusProbability_of_ratios {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (lam : ℕ → Fin (r + 1) → ℕ) (mu : ℕ → Fin r → ℕ)
    (hlam : ∀ i, Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)))
    (hmu : ∀ i, Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i)))
    (i : Fin (r + 1)) :
    Tendsto
      (fun n : ℕ => plusProbability n (lam n) (mu n) i)
      atTop
      (𝓝 (((a i + 1) / (2 * a i + 1)) * lagrangeWeight a b i)) := by
  have hlead := tendsto_plusLeadingFactor_of_ratio
    lam a i (h.ambient_nonneg i) (hlam i)
  have hproduct := tendsto_finsetProd Finset.univ
    (fun j _ => tendsto_channelFactor_of_ratios
      a b h lam mu hlam hmu i j (1 / 2 : ℝ) 0)
  have hlimit := hlead.mul hproduct
  convert hlimit using 1
  · ext n
    unfold plusProbability activeDenominator
    rw [mul_div_mul_comm, ← Finset.prod_div_distrib]
    congr 2
    funext j
    ring
  · unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
    rw [Finset.prod_div_distrib]

theorem tendsto_minusProbability_raiseWeight_of_ratios {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (lam : ℕ → Fin (r + 1) → ℕ) (mu : ℕ → Fin r → ℕ)
    (hlam : ∀ i, Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)))
    (hmu : ∀ i, Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i)))
    (i : Fin (r + 1)) :
    Tendsto
      (fun n : ℕ => minusProbability n
        (raiseWeight (lam n) i) (mu n) i)
      atTop
      (𝓝 ((a i / (2 * a i + 1)) * lagrangeWeight a b i)) := by
  have hlead := tendsto_raisedMinusLeadingFactor_of_ratio
    lam a i (h.ambient_nonneg i) (hlam i)
  have hproduct := tendsto_finsetProd Finset.univ
    (fun j _ => tendsto_channelFactor_of_ratios
      a b h lam mu hlam hmu i j (1 / 2 : ℝ) 1)
  have hlimit := hlead.mul hproduct
  convert hlimit using 1
  · ext n
    unfold minusProbability activeDenominator
    simp_rw [ambientShift_raiseWeight_self,
      ambientShift_raiseWeight_other _ i _ (Fin.succAbove_ne i _)]
    rw [mul_div_mul_comm, ← Finset.prod_div_distrib]
    congr 2
    funext j
    congr 2
    ring
  · unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
    rw [Finset.prod_div_distrib]

theorem tendsto_actualEdgeWeight_of_ratios {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (lam : ℕ → Fin (r + 1) → ℕ) (mu : ℕ → Fin r → ℕ)
    (hlam : ∀ i, Tendsto (fun n : ℕ => (lam n i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)))
    (hmu : ∀ i, Tendsto (fun n : ℕ => (mu n i : ℝ) / (n : ℝ))
      atTop (𝓝 (b i)))
    (i : Fin (r + 1)) :
    Tendsto
      (fun n : ℕ =>
        Real.sqrt
          (plusProbability n (lam n) (mu n) i *
            minusProbability n (raiseWeight (lam n) i) (mu n) i))
      atTop (𝓝 (lagrangeWeight a b i * spectralAtom (a i))) := by
  have hplus := tendsto_plusProbability_of_ratios a b h
    lam mu hlam hmu i
  have hminus := tendsto_minusProbability_raiseWeight_of_ratios
    a b h lam mu hlam hmu i
  have hlimit := (hplus.mul hminus).sqrt
  have ha := h.ambient_nonneg i
  have hw := h.lagrangeWeight_pos i
  have hden : 0 < 2 * a i + 1 := by linarith
  convert hlimit using 1
  have hrad :
      (((a i + 1) / (2 * a i + 1)) * lagrangeWeight a b i) *
          ((a i / (2 * a i + 1)) * lagrangeWeight a b i) =
        (a i * (1 + a i)) *
          (lagrangeWeight a b i / (2 * a i + 1)) ^ 2 := by
    field_simp [hden.ne']
    ring
  rw [hrad, Real.sqrt_mul (mul_nonneg ha (by positivity)),
    Real.sqrt_sq (div_nonneg hw.le hden.le)]
  unfold spectralAtom
  ring_nf

/-- The edge weight used in the spherical-code argument. -/
def edgeWeight {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (n : ℕ) (v : Vertex r m) (i : Fin (r + 1)) : ℝ :=
  Real.sqrt
    (plusProbability n (signature a n v) (flooredCoordinates b n) i *
      minusProbability n (raiseWeight (signature a n v) i)
        (flooredCoordinates b n) i)

theorem tendsto_edgeWeight {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) (v : Vertex r m) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => edgeWeight a b n v i)
      atTop (𝓝 (lagrangeWeight a b i * spectralAtom (a i))) := by
  apply tendsto_actualEdgeWeight_of_ratios a b h
    (fun n => signature a n v) (flooredCoordinates b)
  · intro j
    exact tendsto_signature_ratio a (fun _ => v) j
      (h.ambient_nonneg j)
  · intro j
    exact tendsto_flooredCoordinates_ratio b j
      (h.stabilizer_pos j).le

theorem eventually_edgeWeight_pos_all {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) (ha : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Vertex r m) (i : Fin (r + 1)),
      0 < edgeWeight a b n v i := by
  apply eventually_all.2
  intro v
  apply eventually_all.2
  intro i
  have hai : 0 < a i := ha i
  have hquad : 0 < ((a i) * (1 + (a i))) := by
    exact mul_pos hai (by linarith)
  have hatom : 0 < spectralAtom (a i) := by
    unfold spectralAtom
    exact div_pos (Real.sqrt_pos.mpr hquad) (by linarith)
  exact (tendsto_edgeWeight a b h v i).eventually
    (Ioi_mem_nhds (mul_pos (h.lagrangeWeight_pos i) hatom))

end HigherHierarchy.RectangularVertices

end

section


open Metric
open scoped BigOperators InnerProductSpace Matrix

namespace HigherHierarchyFinitePerron

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The space used in the spherical-code argument. -/
abbrev Space (I : Type*) := EuclideanSpace ℝ I

/-- A nonnegative matrix whose positive-entry quiver is strongly connected. -/
structure ConnectedNonnegativeMatrix (A : Matrix I I ℝ) : Prop where
  nonneg (i j : I) : 0 ≤ A i j
  connected : @Quiver.IsSStronglyConnected I
    ⟨fun i j => PLift (0 < A i j)⟩

/-- The operator used in the spherical-code argument. -/
def operator (A : Matrix I I ℝ) : Space I →ₗ[ℝ] Space I :=
  Matrix.toEuclideanLin A

/-- The continuous operator used in the spherical-code argument. -/
def continuousOperator (A : Matrix I I ℝ) : Space I →L[ℝ] Space I :=
  LinearMap.toContinuousLinearMap (operator A)

/-- The rayleigh used in the spherical-code argument. -/
def rayleigh (A : Matrix I I ℝ) (x : Space I) : ℝ :=
  (continuousOperator A).rayleighQuotient x

omit [Nonempty I] in
theorem rayleigh_bddAbove (A : Matrix I I ℝ) :
    BddAbove
      (Set.range (fun x : {x : Space I // x ≠ 0} => rayleigh A x)) := by
  refine ⟨‖continuousOperator A‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (le_abs_self _).trans
    ((continuousOperator A).rayleighQuotient_le_norm x)

/-- The top eigenvalue used in the spherical-code argument. -/
def topEigenvalue (A : Matrix I I ℝ) : ℝ :=
  ⨆ x : {x : Space I // x ≠ 0}, rayleigh A x

omit [Nonempty I] in
theorem rayleigh_le_top (A : Matrix I I ℝ)
    (x : Space I) (hx : x ≠ 0) :
    rayleigh A x ≤ topEigenvalue A := by
  exact le_ciSup (rayleigh_bddAbove A) ⟨x, hx⟩

omit [Nonempty I] in
theorem operator_isSymmetric (A : Matrix I I ℝ)
    (hA : Aᵀ = A) : (operator A).IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrArg (fun B : Matrix I I ℝ => B i j) hA
  simpa only [star_trivial, Matrix.transpose_apply] using h

theorem exists_topEigenvector (A : Matrix I I ℝ)
    (hA : Aᵀ = A) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x := by
  have h := (operator_isSymmetric A hA).hasEigenvalue_iSup_of_finiteDimensional
  have hvalue :
      Module.End.HasEigenvalue (operator A) (topEigenvalue A) := by
    simpa only [topEigenvalue, ne_eq, rayleigh, ContinuousLinearMap.rayleighQuotient,
      continuousOperator, ContinuousLinearMap.reApplyInnerSelf_apply,
      LinearMap.coe_toContinuousLinearMap', RCLike.re_to_real, Order.lt_one_iff,
      Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one, Real.ringHom_apply] using h
  obtain ⟨x, hx⟩ := hvalue.exists_hasEigenvector
  exact ⟨x, hx.2, hx.apply_eq_smul⟩

/-- The coordinate abs used in the spherical-code argument. -/
def coordinateAbs (x : Space I) : Space I :=
  WithLp.toLp 2 fun i : I => |x i|

omit [DecidableEq I] [Nonempty I] in
theorem coordinateAbs_norm (x : Space I) :
    ‖coordinateAbs x‖ = ‖x‖ := by
  have hsquare : ‖coordinateAbs x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [coordinateAbs, sq_abs]
  nlinarith [norm_nonneg (coordinateAbs x), norm_nonneg x]

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem coordinateAbs_ne_zero {x : Space I} (hx : x ≠ 0) :
    coordinateAbs x ≠ 0 := by
  intro habs
  apply hx
  apply PiLp.ext
  intro i
  have hi := congrArg (fun y : Space I => y i) habs
  simpa only [coordinateAbs, PiLp.zero_apply, abs_eq_zero] using hi

omit [Nonempty I] in
theorem inner_le_inner_coordinateAbs (A : Matrix I I ℝ)
    (hA : ∀ i j : I, 0 ≤ A i j) (x : Space I) :
    @inner ℝ (Space I) _ (operator A x) x ≤
      @inner ℝ (Space I) _ (operator A (coordinateAbs x))
        (coordinateAbs x) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : I, (∑ j : I, A i j * x j) * x i) ≤
      ∑ i : I, (∑ j : I, A i j * |x j|) * |x i|
  simp_rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hproduct : x j * x i ≤ |x j| * |x i| := by
    calc
      x j * x i ≤ |x j * x i| := le_abs_self _
      _ = |x j| * |x i| := abs_mul _ _
  calc
    A i j * x j * x i = A i j * (x j * x i) := by ring
    _ ≤ A i j * (|x j| * |x i|) :=
      mul_le_mul_of_nonneg_left hproduct (hA i j)
    _ = A i j * |x j| * |x i| := by ring

omit [Nonempty I] in
theorem rayleigh_eq_of_eigenvector (A : Matrix I I ℝ)
    (x : Space I) (hx : x ≠ 0) (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x) :
    rayleigh A x = eigenvalue := by
  change @inner ℝ (Space I) _ (operator A x) x / ‖x‖ ^ 2 = eigenvalue
  rw [heig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  field_simp [hnorm]

omit [Nonempty I] in
theorem rayleigh_le_coordinateAbs (A : Matrix I I ℝ)
    (hA : ∀ i j : I, 0 ≤ A i j) (x : Space I) :
    rayleigh A x ≤ rayleigh A (coordinateAbs x) := by
  change
    @inner ℝ (Space I) _ (operator A x) x / ‖x‖ ^ 2 ≤
      @inner ℝ (Space I) _ (operator A (coordinateAbs x))
        (coordinateAbs x) / ‖coordinateAbs x‖ ^ 2
  rw [coordinateAbs_norm]
  gcongr
  exact inner_le_inner_coordinateAbs A hA x

theorem exists_nonnegative_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hnonneg : ∀ i j : I, 0 ≤ A i j) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 ≤ x i := by
  obtain ⟨x, hx, heig⟩ := exists_topEigenvector A hsymm
  let y : Space I := coordinateAbs x
  have hy : y ≠ 0 := coordinateAbs_ne_zero hx
  have hbelow := rayleigh_le_coordinateAbs A hnonneg x
  have habove := rayleigh_le_top A y hy
  have hxray := rayleigh_eq_of_eigenvector A x hx (topEigenvalue A) heig
  rw [hxray] at hbelow
  have hyray : rayleigh A y = topEigenvalue A :=
    le_antisymm habove hbelow
  have hself : IsSelfAdjoint (continuousOperator A) :=
    (operator_isSymmetric A hsymm).isSelfAdjoint
  have hmax :
      IsMaxOn (continuousOperator A).reApplyInnerSelf
        (sphere (0 : Space I) ‖y‖) y := by
    intro z hz
    have hnorm : ‖z‖ = ‖y‖ := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hznonzero : z ≠ 0 := by
      intro hzzero
      rw [hzzero, norm_zero] at hnorm
      exact hy (norm_eq_zero.mp hnorm.symm)
    have hray := rayleigh_le_top A z hznonzero
    rw [← hyray] at hray
    change
      (continuousOperator A).reApplyInnerSelf z / ‖z‖ ^ 2 ≤
        (continuousOperator A).reApplyInnerSelf y / ‖y‖ ^ 2 at hray
    rw [hnorm] at hray
    exact (div_le_div_iff_of_pos_right
      (sq_pos_of_pos (norm_pos_iff.mpr hy))).mp hray
  have heigy := hself.hasEigenvector_of_isMaxOn hy hmax
  refine ⟨y, hy, ?_, fun i => abs_nonneg (x i)⟩
  have happly := heigy.apply_eq_smul
  simpa only [topEigenvalue, ne_eq, rayleigh, continuousOperator,
    LinearMap.coe_toContinuousLinearMap, Real.ringHom_apply] using happly

omit [Nonempty I] in
theorem eigenvector_zero_of_positive_edge (A : Matrix I I ℝ)
    (hnonneg : ∀ i j : I, 0 ≤ A i j)
    (x : Space I) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x)
    {i j : I} (hzero : x i = 0) (hedge : 0 < A i j) :
    x j = 0 := by
  have hrow := congrArg (fun z : Space I => z i) heig
  change (∑ k : I, A i k * x k) = eigenvalue * x i at hrow
  rw [hzero, mul_zero] at hrow
  have hsingle : A i j * x j ≤ ∑ k : I, A i k * x k := by
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (hnonneg i k) (hx k))
      (Finset.mem_univ j)
  rw [hrow] at hsingle
  have hterm : A i j * x j = 0 :=
    le_antisymm hsingle (mul_nonneg (hnonneg i j) (hx j))
  exact (mul_eq_zero.mp hterm).resolve_left hedge.ne'

omit [Nonempty I] in
theorem eigenvector_zero_of_positive_path (A : Matrix I I ℝ)
    (hnonneg : ∀ i j : I, 0 ≤ A i j)
    (x : Space I) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x)
    {i j : I} (p : @Quiver.Path I ⟨fun u v => PLift (0 < A u v)⟩ i j)
    (hzero : x i = 0) : x j = 0 := by
  induction p with
  | nil => exact hzero
  | @cons j k p e ih =>
      exact eigenvector_zero_of_positive_edge A hnonneg x hx
        eigenvalue heig ih e.down

omit [Nonempty I] in
theorem eigenvector_pos_of_irreducible (A : Matrix I I ℝ)
    (hirreducible : ConnectedNonnegativeMatrix A)
    (x : Space I) (hxzero : x ≠ 0) (hx : ∀ i : I, 0 ≤ x i)
    (eigenvalue : ℝ)
    (heig : operator A x = eigenvalue • x) :
    ∀ i : I, 0 < x i := by
  intro i
  by_contra hnot
  have hzero : x i = 0 :=
    le_antisymm (le_of_not_gt hnot) (hx i)
  apply hxzero
  apply PiLp.ext
  intro j
  obtain ⟨p, _⟩ := hirreducible.connected i j
  simpa only [PiLp.zero_apply] using
    eigenvector_zero_of_positive_path A hirreducible.nonneg x hx eigenvalue heig p hzero

theorem exists_positive_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hirreducible : ConnectedNonnegativeMatrix A) :
    ∃ x : Space I, x ≠ 0 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 < x i := by
  obtain ⟨x, hx, heig, hnonneg⟩ :=
    exists_nonnegative_topEigenvector A hsymm hirreducible.nonneg
  exact ⟨x, hx, heig,
    eigenvector_pos_of_irreducible A hirreducible x hx hnonneg
      (topEigenvalue A) heig⟩

theorem exists_positive_unit_topEigenvector (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hirreducible : ConnectedNonnegativeMatrix A) :
    ∃ x : Space I,
      ‖x‖ = 1 ∧
      operator A x = topEigenvalue A • x ∧ ∀ i : I, 0 < x i := by
  obtain ⟨x, hx, heig, hpos⟩ :=
    exists_positive_topEigenvector A hsymm hirreducible
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖⁻¹ • x, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
    exact inv_mul_cancel₀ hnorm.ne'
  · rw [map_smul, heig]
    exact smul_comm _ _ _
  · intro i
    change 0 < ‖x‖⁻¹ * x i
    exact mul_pos (inv_pos.mpr hnorm) (hpos i)

omit [DecidableEq I] [Nonempty I] in
theorem unit_coordinate_sq_sum {x : Space I} (hx : ‖x‖ = 1) :
    (∑ i : I, x i ^ 2) = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, hx]
  norm_num

theorem exists_positive_unit_topEigenpair (A : Matrix I I ℝ)
    (hsymm : Aᵀ = A) (hirreducible : ConnectedNonnegativeMatrix A) :
    ∃ x : I → ℝ,
      (∀ i : I, 0 < x i) ∧
      (∑ i : I, x i ^ 2) = 1 ∧
      (∀ i : I, ∑ j : I, A i j * x j = topEigenvalue A * x i) := by
  obtain ⟨x, hunit, heig, hpos⟩ :=
    exists_positive_unit_topEigenvector A hsymm hirreducible
  refine ⟨fun i => x i, hpos, unit_coordinate_sq_sum hunit, ?_⟩
  intro i
  have h := congrArg (fun z : Space I => z i) heig
  exact h

end HigherHierarchyFinitePerron

end

section


open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology

namespace HigherHierarchyTrueGridAdjacency

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral

/-- The vertex used in the spherical-code argument. -/
abbrev Vertex (r m : ℕ) := BoxVertex r m

/-- The signature used in the spherical-code argument. -/
def signature {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (n : ℕ) (v : Vertex r m) :
    Fin (r + 1) → ℕ :=
  fun i => flooredCoordinates a n i + (v i).val

theorem signature_nextVertex {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (n : ℕ) (v : Vertex r m)
    (i : Fin (r + 1)) (h : (v i).val < m) :
    signature a n (nextVertex v i h) = raiseWeight (signature a n v) i := by
  funext j
  by_cases hji : j = i
  · subst j
    simp only [signature, nextVertex, Function.update_self, raiseWeight]
    omega
  · simp only [signature, nextVertex, ne_eq, hji, not_false_eq_true, Function.update_of_ne,
      raiseWeight]

/-- The edge weight used in the spherical-code argument. -/
def edgeWeight {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (n : ℕ) (v : Vertex r m) (i : Fin (r + 1)) : ℝ :=
  Real.sqrt
    (plusProbability n (signature a n v) (flooredCoordinates b n) i *
      minusProbability n (raiseWeight (signature a n v) i)
        (flooredCoordinates b n) i)

theorem edgeWeight_nonneg {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (n : ℕ) (v : Vertex r m) (i : Fin (r + 1)) :
    0 ≤ edgeWeight a b n v i := Real.sqrt_nonneg _

/-- The matrix used in the spherical-code argument. -/
def matrix {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ) :
    Matrix (Vertex r m) (Vertex r m) ℝ :=
  adjacencyMatrix (edgeWeight (m := m) a b n)

theorem matrix_symmetric {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ) :
    (matrix (m := m) a b n)ᵀ = matrix a b n :=
  adjacencyMatrix_transpose _

theorem matrix_nonneg {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v w : Vertex r m) : 0 ≤ matrix a b n v w := by
  change
    0 ≤ forwardMatrix (edgeWeight (m := m) a b n) v w +
      forwardMatrix (edgeWeight (m := m) a b n) w v
  apply add_nonneg
  · unfold forwardMatrix
    simp only [Matrix.of_apply]
    exact Finset.sum_nonneg fun i _ => by
      split_ifs <;> first | exact edgeWeight_nonneg a b n v i | exact le_rfl
  · unfold forwardMatrix
    simp only [Matrix.of_apply]
    exact Finset.sum_nonneg fun i _ => by
      split_ifs <;> first | exact edgeWeight_nonneg a b n w i | exact le_rfl

/-- The grid used in the spherical-code argument. -/
def grid (r m : ℕ) : SimpleGraph (Vertex r m) where
  Adj v w :=
    ∃ i : Fin (r + 1),
      (∃ h : (v i).val < m, w = nextVertex v i h) ∨
      (∃ h : (w i).val < m, v = nextVertex w i h)
  symm := ⟨by
    intro v w ⟨i, h⟩
    exact ⟨i, h.symm⟩⟩
  loopless := ⟨by
    intro v hv
    obtain ⟨i, h | h⟩ := hv
    · obtain ⟨_, hv⟩ := h
      have hval := congrArg (fun z : Vertex r m => (z i).val) hv
      simp only [nextVertex, Function.update_self, Nat.left_eq_add, one_ne_zero] at hval
    · obtain ⟨_, hv⟩ := h
      have hval := congrArg (fun z : Vertex r m => (z i).val) hv
      simp only [nextVertex, Function.update_self, Nat.left_eq_add, one_ne_zero] at hval⟩

theorem grid_adj_nextVertex {r m : ℕ}
    (v : Vertex r m) (i : Fin (r + 1)) (h : (v i).val < m) :
    (grid r m).Adj v (nextVertex v i h) :=
  ⟨i, Or.inl ⟨h, rfl⟩⟩

private def height {r m : ℕ} (v : Vertex r m) : ℕ :=
  ∑ i : Fin (r + 1), (v i).val

theorem reachable_zero {r m : ℕ} (v : Vertex r m) :
    (grid r m).Reachable (fun _ => 0) v := by
  classical
  induction hN : height v using Nat.strong_induction_on generalizing v with
  | h N ih =>
      by_cases hz : v = (fun _ => 0)
      · subst v
        exact SimpleGraph.Reachable.rfl
      · have hpositive : ∃ i : Fin (r + 1), 0 < (v i).val := by
          by_contra hnot
          apply hz
          funext i
          apply Fin.ext
          apply Nat.eq_zero_of_not_pos
          intro hi
          exact hnot ⟨i, hi⟩
        obtain ⟨i, hi⟩ := hpositive
        let u : Vertex r m :=
          Function.update v i ⟨(v i).val - 1, by omega⟩
        have hu : height u < height v := by
          unfold height
          change
            (∑ j : Fin (r + 1),
              (Function.update v i
                (⟨(v i).val - 1, by omega⟩ : Fin (m + 1)) j).val) <
              ∑ j : Fin (r + 1), (v j).val
          have hpoint (j : Fin (r + 1)) :
              (Function.update v i
                (⟨(v i).val - 1, by omega⟩ : Fin (m + 1)) j).val =
                Function.update (fun k : Fin (r + 1) => (v k).val)
                  i ((v i).val - 1) j := by
            by_cases hji : j = i
            · subst j
              simp only [Function.update_self]
            · simp only [Function.update_of_ne hji]
          simp_rw [hpoint]
          rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
          have hold :=
            Finset.sum_erase_add (Finset.univ : Finset (Fin (r + 1)))
              (fun j => (v j).val) (Finset.mem_univ i)
          rw [Finset.sdiff_singleton_eq_erase]
          omega
        have hless : height u < N := hN ▸ hu
        have hreach := ih (height u) hless u rfl
        have hstep : (u i).val < m := by
          dsimp [u]
          simp only [Function.update_self]
          omega
        have heq : nextVertex u i hstep = v := by
          funext j
          by_cases hji : j = i
          · subst j
            apply Fin.ext
            simp only [nextVertex, Function.update_self, u]
            omega
          · simp only [nextVertex, Function.update_self, ne_eq, hji, not_false_eq_true,
              Function.update_of_ne, u]
        have hedge : (grid r m).Reachable u v := by
          rw [← heq]
          exact (grid_adj_nextVertex u i hstep).reachable
        exact hreach.trans hedge

theorem grid_connected (r m : ℕ) : (grid r m).Connected := by
  apply (grid r m).connected_iff_exists_forall_reachable.mpr
  exact ⟨(fun _ => 0), reachable_zero⟩

private theorem forwardMatrix_nextVertex_pos_metriccodes2_dbb1ceac {r m : ℕ}
    (edge : Vertex r m → Fin (r + 1) → ℝ)
    (hpositive : ∀ v i, (v i).val < m → 0 < edge v i)
    (v : Vertex r m) (i : Fin (r + 1)) (h : (v i).val < m) :
    0 < forwardMatrix edge v (nextVertex v i h) := by
  unfold forwardMatrix
  simp only [Matrix.of_apply]
  apply (Finset.sum_pos_iff_of_nonneg ?_).2
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [h, ↓reduceDIte, ↓reduceIte, hpositive v i h]
  · intro j _
    split_ifs with hj heq
    · exact (hpositive v j hj).le
    · exact le_rfl
    · exact le_rfl

private theorem adjacencyMatrix_nextVertex_pos_metriccodes2_dbb1ceac {r m : ℕ}
    (edge : Vertex r m → Fin (r + 1) → ℝ)
    (hpositive : ∀ v i, (v i).val < m → 0 < edge v i)
    (v : Vertex r m) (i : Fin (r + 1)) (h : (v i).val < m) :
    0 < adjacencyMatrix edge v (nextVertex v i h) := by
  have hf := forwardMatrix_nextVertex_pos_metriccodes2_dbb1ceac edge hpositive v i h
  have hr : 0 ≤ forwardMatrix edge (nextVertex v i h) v := by
    unfold forwardMatrix
    simp only [Matrix.of_apply]
    exact Finset.sum_nonneg fun j _ => by
      split_ifs with hj heq
      · exact (hpositive (nextVertex v i h) j hj).le
      · exact le_rfl
      · exact le_rfl
  exact lt_of_lt_of_le hf (le_add_of_nonneg_right hr)

theorem matrix_pos_of_grid_adj {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (hpositive : ∀ (v : Vertex r m) (i : Fin (r + 1)),
      (v i).val < m → 0 < edgeWeight a b n v i)
    {v w : Vertex r m} (hadj : (grid r m).Adj v w) :
    0 < matrix a b n v w := by
  obtain ⟨i, h | h⟩ := hadj
  · obtain ⟨hi, rfl⟩ := h
    exact adjacencyMatrix_nextVertex_pos_metriccodes2_dbb1ceac _ hpositive v i hi
  · obtain ⟨hi, rfl⟩ := h
    have hsym := congrArg
      (fun A : Matrix (Vertex r m) (Vertex r m) ℝ =>
        A w (nextVertex w i hi))
      (matrix_symmetric (m := m) a b n)
    change matrix a b n (nextVertex w i hi) w =
      matrix a b n w (nextVertex w i hi) at hsym
    rw [hsym]
    exact adjacencyMatrix_nextVertex_pos_metriccodes2_dbb1ceac _ hpositive w i hi

private theorem matrix_irreducible_of_connected_metriccodes2_dbb1ceac
    {V : Type*}
    (G : SimpleGraph V) (hconnected : G.Connected)
    (A : Matrix V V ℝ)
    (hnonneg : ∀ v w, 0 ≤ A v w)
    (hedge : ∀ {v w}, G.Adj v w → 0 < A v w)
    (hexists : ∃ v w, G.Adj v w) :
    HigherHierarchyFinitePerron.ConnectedNonnegativeMatrix A := by
  refine ⟨hnonneg, ?_⟩
  let : Quiver V := ⟨fun v w => PLift (0 < A v w)⟩
  have hstrong : Quiver.IsStronglyConnected V := by
    intro v w
    obtain ⟨p⟩ := hconnected.preconnected v w
    induction p with
    | nil => exact ⟨Quiver.Path.nil⟩
    | @cons u v w huv p ih =>
        exact ⟨(Quiver.Hom.toPath (PLift.up (hedge huv))).comp ih.some⟩
  obtain ⟨v, w, hvw⟩ := hexists
  exact hstrong.isSStronglyConnected_of_hom (PLift.up (hedge hvw))

theorem matrix_irreducible {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (hm : 0 < m)
    (hpositive : ∀ (v : Vertex r m) (i : Fin (r + 1)),
      (v i).val < m → 0 < edgeWeight a b n v i) :
    HigherHierarchyFinitePerron.ConnectedNonnegativeMatrix
      (matrix (m := m) a b n) := by
  apply matrix_irreducible_of_connected_metriccodes2_dbb1ceac (grid r m)
    (grid_connected r m) (matrix a b n) (matrix_nonneg a b n)
    (matrix_pos_of_grid_adj a b n hpositive)
  let v : Vertex r m := fun _ => 0
  have hv : (v (0 : Fin (r + 1))).val < m := by
    simpa [v] using hm
  exact ⟨v, nextVertex v 0 hv, grid_adj_nextVertex v 0 hv⟩

theorem eventually_matrix_irreducible {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) (ha : ∀ i, 0 < a i)
    (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      HigherHierarchyFinitePerron.ConnectedNonnegativeMatrix
        (matrix (m := m) a b n) := by
  filter_upwards
    [MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_edgeWeight_pos_all
      (m := m) a b h ha] with n hn
  apply matrix_irreducible a b n hm
  intro v i _
  exact hn v i

end HigherHierarchyTrueGridAdjacency

end

section


open scoped BigOperators Matrix

namespace HigherHierarchyBoxChannels

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency

/-- The plus edge used in the spherical-code argument. -/
def plusEdge {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v : Vertex r m) (i : Fin (r + 1)) : ℝ :=
  plusProbability n (signature a n v) (flooredCoordinates b n) i

/-- The minus edge used in the spherical-code argument. -/
def minusEdge {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v : Vertex r m) (i : Fin (r + 1)) : ℝ :=
  minusProbability n (raiseWeight (signature a n v) i)
    (flooredCoordinates b n) i

/-- The probability used in the spherical-code argument. -/
def probability {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v w : Vertex r m) : ℝ :=
  forwardMatrix (plusEdge (m := m) a b n) v w +
    forwardMatrix (minusEdge (m := m) a b n) w v

private def vertexWeylDimension {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (n : ℕ) (v : Vertex r m) : ℝ :=
  Weyl.dimension n (signature a n v)

theorem nextVertex_direction_injective {r m : ℕ}
    (v : Vertex r m) (i j : Fin (r + 1))
    (hi : (v i).val < m) (hj : (v j).val < m)
    (heq : nextVertex v i hi = nextVertex v j hj) : i = j := by
  by_contra hne
  have hcoord := congrArg (fun z : Vertex r m => (z i).val) heq
  simp only [nextVertex, Function.update_self, Function.update_of_ne hne, Nat.add_eq_left,
    one_ne_zero] at hcoord

theorem nextVertex_not_forward_back {r m : ℕ}
    (v : Vertex r m) (i j : Fin (r + 1))
    (hi : (v i).val < m)
    (hj : (nextVertex v i hi j).val < m) :
    v ≠ nextVertex (nextVertex v i hi) j hj := by
  intro heq
  have hcoord := congrArg (fun z : Vertex r m => (z j).val) heq
  by_cases hji : j = i
  · subst j
    simp only [nextVertex, Function.update_self] at hcoord
    omega
  · simp only [nextVertex, Function.update_of_ne hji, Function.update_self, Nat.left_eq_add,
      one_ne_zero] at hcoord

theorem forwardMatrix_nextVertex {r m : ℕ}
    (edge : Vertex r m → Fin (r + 1) → ℝ)
    (v : Vertex r m) (i : Fin (r + 1))
    (hi : (v i).val < m) :
    forwardMatrix edge v (nextVertex v i hi) = edge v i := by
  classical
  unfold forwardMatrix
  simp only [Matrix.of_apply]
  rw [Finset.sum_eq_single i]
  · simp only [hi, ↓reduceDIte, ↓reduceIte]
  · intro j _ hji
    by_cases hj : (v j).val < m
    · simp only [dite_eq_left hj]
      split_ifs with heq
      · exact (hji (nextVertex_direction_injective v j i hj hi
          heq.symm)).elim
      · rfl
    · simp only [hj, ↓reduceDIte]
  · simp only [Finset.mem_univ, not_true_eq_false, ↓reduceIte, dite_eq_ite, ite_eq_right_iff,
      IsEmpty.forall_iff]

theorem forwardMatrix_nextVertex_reverse {r m : ℕ}
    (edge : Vertex r m → Fin (r + 1) → ℝ)
    (v : Vertex r m) (i : Fin (r + 1))
    (hi : (v i).val < m) :
    forwardMatrix edge (nextVertex v i hi) v = 0 := by
  classical
  unfold forwardMatrix
  simp only [Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro j _
  split_ifs with hj heq
  · exact (nextVertex_not_forward_back v i j hi hj heq).elim
  · rfl
  · rfl

theorem probability_nextVertex {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v : Vertex r m) (i : Fin (r + 1))
    (hi : (v i).val < m) :
    probability a b n v (nextVertex v i hi) = plusEdge a b n v i := by
  unfold probability
  rw [forwardMatrix_nextVertex, forwardMatrix_nextVertex_reverse]
  simp only [add_zero]

theorem probability_nextVertex_reverse {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v : Vertex r m) (i : Fin (r + 1))
    (hi : (v i).val < m) :
    probability a b n (nextVertex v i hi) v = minusEdge a b n v i := by
  unfold probability
  rw [forwardMatrix_nextVertex_reverse, forwardMatrix_nextVertex]
  simp only [zero_add]

theorem probability_eq_zero_of_not_adjacent {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v w : Vertex r m)
    (h : ¬ (grid r m).Adj v w) : probability a b n v w = 0 := by
  classical
  unfold probability forwardMatrix
  simp only [Matrix.of_apply]
  have hforward :
      (∑ i : Fin (r + 1),
        if hi : (v i).val < m then
          if w = nextVertex v i hi then plusEdge a b n v i else 0
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi heq
    · exact (h ⟨i, Or.inl ⟨hi, heq⟩⟩).elim
    · rfl
    · rfl
  have hreverse :
      (∑ i : Fin (r + 1),
        if hi : (w i).val < m then
          if v = nextVertex w i hi then minusEdge a b n w i else 0
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi heq
    · exact (h ⟨i, Or.inr ⟨hi, heq⟩⟩).elim
    · rfl
    · rfl
  rw [hforward, hreverse]
  norm_num

theorem probability_nonneg {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (hinterlacing : ∀ v : Vertex r m,
      FiniteInterlacing n (signature a n v) (flooredCoordinates b n))
    (v w : Vertex r m) : 0 ≤ probability a b n v w := by
  classical
  by_cases hadj : (grid r m).Adj v w
  · obtain ⟨i, h | h⟩ := hadj
    · obtain ⟨hi, rfl⟩ := h
      rw [probability_nextVertex]
      exact (hinterlacing v).plusProbability_nonneg i
    · obtain ⟨hi, rfl⟩ := h
      rw [probability_nextVertex_reverse]
      unfold minusEdge
      rw [← signature_nextVertex a n w i hi]
      exact (hinterlacing (nextVertex w i hi)).minusProbability_nonneg i
  · rw [probability_eq_zero_of_not_adjacent a b n v w hadj]

theorem weyl_detailed_balance {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (hinterlacing : ∀ v : Vertex r m,
      FiniteInterlacing n (signature a n v) (flooredCoordinates b n))
    (v w : Vertex r m) :
    vertexWeylDimension a n v * probability a b n v w =
      vertexWeylDimension a n w * probability a b n w v := by
  classical
  by_cases hadj : (grid r m).Adj v w
  · obtain ⟨i, h | h⟩ := hadj
    · obtain ⟨hi, rfl⟩ := h
      rw [probability_nextVertex, probability_nextVertex_reverse]
      unfold vertexWeylDimension plusEdge minusEdge
      rw [signature_nextVertex]
      exact actual_weyl_detailed_balance i (hinterlacing v)
        (by simpa only [signature_nextVertex] using hinterlacing (nextVertex v i hi))
    · obtain ⟨hi, rfl⟩ := h
      rw [probability_nextVertex_reverse, probability_nextVertex]
      unfold vertexWeylDimension plusEdge minusEdge
      rw [signature_nextVertex]
      exact (actual_weyl_detailed_balance i (hinterlacing w)
        (by simpa only [signature_nextVertex] using hinterlacing (nextVertex w i hi))).symm
  · have hreverse : ¬ (grid r m).Adj w v := by
      intro h'
      exact hadj h'.symm
    rw [probability_eq_zero_of_not_adjacent a b n v w hadj,
      probability_eq_zero_of_not_adjacent a b n w v hreverse]
    simp only [mul_zero]

theorem symmetric_probability_eq_trueGrid {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v w : Vertex r m) :
    Real.sqrt (probability a b n v w * probability a b n w v) =
      HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n v w := by
  classical
  by_cases hadj : (grid r m).Adj v w
  · obtain ⟨i, h | h⟩ := hadj
    · obtain ⟨hi, rfl⟩ := h
      rw [probability_nextVertex, probability_nextVertex_reverse]
      unfold HigherHierarchyTrueGridAdjacency.matrix adjacencyMatrix
      simp only [Matrix.add_apply, Matrix.transpose_apply]
      rw [forwardMatrix_nextVertex, forwardMatrix_nextVertex_reverse]
      simp only [plusEdge, minusEdge, edgeWeight, add_zero]
    · obtain ⟨hi, rfl⟩ := h
      rw [probability_nextVertex_reverse, probability_nextVertex]
      unfold HigherHierarchyTrueGridAdjacency.matrix adjacencyMatrix
      simp only [Matrix.add_apply, Matrix.transpose_apply]
      rw [forwardMatrix_nextVertex_reverse, forwardMatrix_nextVertex]
      simp only [minusEdge, plusEdge, mul_comm, edgeWeight, zero_add]
  · have hreverse : ¬ (grid r m).Adj w v := by
      intro h'
      exact hadj h'.symm
    rw [probability_eq_zero_of_not_adjacent a b n v w hadj,
      probability_eq_zero_of_not_adjacent a b n w v hreverse]
    simp only [zero_mul, Real.sqrt_zero]
    unfold HigherHierarchyTrueGridAdjacency.matrix adjacencyMatrix
      forwardMatrix
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
    have hforward :
        (∑ i : Fin (r + 1),
          if hi : (v i).val < m then
            if w = nextVertex v i hi then
              HigherHierarchyTrueGridAdjacency.edgeWeight a b n v i
            else 0
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi heq
      · exact (hadj ⟨i, Or.inl ⟨hi, heq⟩⟩).elim
      · rfl
      · rfl
    have hback :
        (∑ i : Fin (r + 1),
          if hi : (w i).val < m then
            if v = nextVertex w i hi then
              HigherHierarchyTrueGridAdjacency.edgeWeight a b n w i
            else 0
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      split_ifs with hi heq
      · exact (hadj ⟨i, Or.inr ⟨hi, heq⟩⟩).elim
      · rfl
      · rfl
    rw [hforward, hback]
    norm_num

end HigherHierarchyBoxChannels

end

section


open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology

namespace HigherHierarchyBoxPerron

open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral

private def constantVector (r m : ℕ) :
    HigherHierarchyFinitePerron.Space (BoxVertex r m) :=
  WithLp.toLp 2 fun _ : BoxVertex r m => (1 : ℝ)

theorem constantVector_ne_zero (r m : ℕ) :
    constantVector r m ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun x : HigherHierarchyFinitePerron.Space (BoxVertex r m) =>
    x (fun _ => 0)) hzero
  simp only [constantVector, PiLp.zero_apply, one_ne_zero] at h

theorem constantVector_norm_sq (r m : ℕ) :
    ‖constantVector r m‖ ^ 2 =
      (Fintype.card (BoxVertex r m) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [constantVector, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Fintype.card_fin, Finset.prod_const, nsmul_eq_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    mul_one]

theorem constantVector_rayleigh {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    HigherHierarchyFinitePerron.rayleigh
      (adjacencyMatrix edge) (constantVector r m) =
      constantRayleigh edge := by
  change
    @inner ℝ (HigherHierarchyFinitePerron.Space (BoxVertex r m)) _
      (HigherHierarchyFinitePerron.operator
        (adjacencyMatrix edge) (constantVector r m))
      (constantVector r m) /
        ‖constantVector r m‖ ^ 2 = constantRayleigh edge
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ v : BoxVertex r m,
      (∑ w : BoxVertex r m,
        adjacencyMatrix edge v w * (1 : ℝ)) * (1 : ℝ)) /
          ‖constantVector r m‖ ^ 2 = constantRayleigh edge
  simp only [mul_one]
  rw [constantVector_norm_sq]
  rfl

theorem constantRayleigh_le_top {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    constantRayleigh edge ≤
      HigherHierarchyFinitePerron.topEigenvalue (adjacencyMatrix edge) := by
  rw [← constantVector_rayleigh]
  exact HigherHierarchyFinitePerron.rayleigh_le_top (adjacencyMatrix edge)
    (constantVector r m) (constantVector_ne_zero r m)

theorem boxWidth_ratio_tendsto :
    Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1))
      atTop (nhds 1) := by
  have hden : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv := tendsto_inv_atTop_zero.comp hden
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlimit := hone.sub hinv
  convert hlimit using 1
  · ext m
    dsimp [Function.comp_def]
    have hden' : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

theorem exists_boxWidth_spectral_gap
    {s gamma : ℝ} (hspectral : s < 2 * gamma) :
    ∃ m : ℕ, 0 < m ∧
      s < (2 * (m : ℝ) / (m + 1 : ℝ)) * gamma := by
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hfactor := (htwo.mul boxWidth_ratio_tendsto).mul_const gamma
  have hlimit :
      Tendsto (fun m : ℕ =>
        (2 * (m : ℝ) / (m + 1 : ℝ)) * gamma)
        atTop (nhds (2 * gamma)) := by
    convert hfactor using 1
    · ext m
      ring
    · ring_nf
  obtain ⟨m, hm, hpos⟩ :=
    ((hlimit.eventually (Ioi_mem_nhds hspectral)).and
      (eventually_gt_atTop (0 : ℕ))).exists
  exact ⟨m, hpos, hm⟩

theorem eventually_topEigenvalue_gt_of_edge_limits {r m : ℕ}
    (edge : ℕ → BoxVertex r m → Fin (r + 1) → ℝ)
    (weight : Fin (r + 1) → ℝ)
    (hlimit : ∀ (v : BoxVertex r m) (i : Fin (r + 1)),
      Tendsto (fun n : ℕ => edge n v i) atTop (nhds (weight i)))
    {s : ℝ}
    (hspectral :
      s < (2 * (m : ℝ) / (m + 1 : ℝ)) *
        ∑ i : Fin (r + 1), weight i) :
    ∀ᶠ n : ℕ in atTop,
      s < HigherHierarchyFinitePerron.topEigenvalue
        (adjacencyMatrix (edge n)) := by
  have h := (constantRayleigh_tendsto edge weight hlimit).eventually
    (Ioi_mem_nhds hspectral)
  filter_upwards [h] with n hn
  exact hn.trans_le (constantRayleigh_le_top (edge n))

theorem exists_boxWidth_eventually_actual_topEigenvalue_gt {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {s : ℝ}
    (hspectral : s < 2 * HigherHierarchy.Gamma a b) :
    ∃ m : ℕ, 0 < m ∧
      ∀ᶠ n : ℕ in atTop,
        s < HigherHierarchyFinitePerron.topEigenvalue
          (adjacencyMatrix
            (HigherHierarchy.RectangularVertices.edgeWeight
              (m := m) a b n)) := by
  obtain ⟨m, hm, hmargin⟩ :=
    exists_boxWidth_spectral_gap hspectral
  refine ⟨m, hm, ?_⟩
  apply eventually_topEigenvalue_gt_of_edge_limits
    (HigherHierarchy.RectangularVertices.edgeWeight (m := m) a b)
    (fun i => lagrangeWeight a b i * spectralAtom (a i))
    (fun v i =>
      HigherHierarchy.RectangularVertices.tendsto_edgeWeight a b h v i)
  simpa only [HigherHierarchy.Gamma] using hmargin

theorem trueGrid_matrix_eq_rectangular {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ) :
    HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n =
      adjacencyMatrix
        (HigherHierarchy.RectangularVertices.edgeWeight
          (m := m) a b n) := by
  rfl

theorem exists_boxWidth_eventually_positive_eigenpair_gt {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ha : ∀ i, 0 < a i)
    {s : ℝ} (hspectral : s < 2 * HigherHierarchy.Gamma a b) :
    ∃ m : ℕ, 0 < m ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (eigenvalue : ℝ) (x : BoxVertex r m → ℝ),
          s < eigenvalue ∧
          (∀ v : BoxVertex r m, 0 < x v) ∧
          (∑ v : BoxVertex r m, x v ^ 2) = 1 ∧
          (∀ v : BoxVertex r m,
            ∑ w : BoxVertex r m,
                HigherHierarchyTrueGridAdjacency.matrix
                  (m := m) a b n v w * x w =
              eigenvalue * x v) := by
  obtain ⟨m, hm, hspectral'⟩ :=
    exists_boxWidth_eventually_actual_topEigenvalue_gt h hspectral
  refine ⟨m, hm, ?_⟩
  have hirreducible :=
    HigherHierarchyTrueGridAdjacency.eventually_matrix_irreducible
      (m := m) a b h ha hm
  filter_upwards [hspectral', hirreducible] with n hgap hconnected
  let A : Matrix (BoxVertex r m) (BoxVertex r m) ℝ :=
    HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n
  obtain ⟨x, hpositive, hunit, heigen⟩ :=
    HigherHierarchyFinitePerron.exists_positive_unit_topEigenpair
      A (HigherHierarchyTrueGridAdjacency.matrix_symmetric a b n)
      hconnected
  refine ⟨HigherHierarchyFinitePerron.topEigenvalue A,
    x, ?_, hpositive, hunit, heigen⟩
  change
    s < HigherHierarchyFinitePerron.topEigenvalue
      (HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n)
  rw [trueGrid_matrix_eq_rectangular]
  exact hgap

theorem exists_boxWidth_positive_gap_eventually_positive_eigenpair {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ha : ∀ i, 0 < a i)
    {s : ℝ} (hspectral : s < 2 * HigherHierarchy.Gamma a b) :
    ∃ (m : ℕ) (gap : ℝ), 0 < m ∧ 0 < gap ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (eigenvalue : ℝ) (x : BoxVertex r m → ℝ),
          s + gap < eigenvalue ∧
          (∀ v : BoxVertex r m, 0 < x v) ∧
          (∑ v : BoxVertex r m, x v ^ 2) = 1 ∧
          (∀ v : BoxVertex r m,
            ∑ w : BoxVertex r m,
                HigherHierarchyTrueGridAdjacency.matrix
                  (m := m) a b n v w * x w =
              eigenvalue * x v) := by
  let gap : ℝ := (2 * HigherHierarchy.Gamma a b - s) / 2
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hthreshold : s + gap < 2 * HigherHierarchy.Gamma a b := by
    dsimp [gap]
    linarith
  obtain ⟨m, hm, heigen⟩ :=
    exists_boxWidth_eventually_positive_eigenpair_gt h ha hthreshold
  exact ⟨m, gap, hm, hgap, heigen⟩

end HigherHierarchyBoxPerron

end

namespace HigherHierarchy

section


open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherChannel

theorem interlacing_strictAnti_stabilizer {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : StrictAnti b := by
  cases r with
  | zero => exact fun i => Fin.elim0 i
  | succ r =>
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      have hlow := (h.2 i.succ).1
      have hhigh := (h.2 i.castSucc).2
      have hindex : i.succ.castSucc = i.castSucc.succ := by
        apply Fin.ext
        simp only [Fin.castSucc_succ, Fin.val_succ, Fin.val_castSucc]
      rw [hindex] at hlow
      exact hlow.trans hhigh

theorem tendsto_flooredCoordinates_succ_ratio {I : Type*}
    (a : I → ℝ) (i : I) (ha : 0 ≤ a i) :
    Tendsto
      (fun n : ℕ =>
        (flooredCoordinates a (n + 1) i : ℝ) / (n : ℝ))
      atTop (nhds (a i)) := by
  have hweight := (tendsto_flooredCoordinates_ratio a i ha).comp
    (tendsto_add_atTop_nat 1)
  have hratio :
      Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
        atTop (nhds (1 : ℝ)) := by
    have h := SpherePacking.tendsto_natCast_div_self.add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    convert h using 1
    · ext n
      push_cast
      ring
    · norm_num
  have hproduct := hweight.mul hratio
  have heq :
      (fun n : ℕ =>
        ((flooredCoordinates a (n + 1) i : ℝ) /
          ((n + 1 : ℕ) : ℝ)) *
            (((n + 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (flooredCoordinates a (n + 1) i : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    have hsucc : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [mul_one] using hproduct.congr' heq

theorem tendsto_log_stabilizerDimension_floor_current_div_log_two
    {r : ℕ} (b : Fin (r + 1) → ℝ)
    (hb : ∀ i, 0 < b i) (hanti : StrictAnti b) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (Weyl.dimension (n - 1) (Weyl.flooredWeight b n)) /
          (n : ℝ)) / Real.log 2)
      atTop (nhds (∑ i : Fin (r + 1), MetricCodes.sphericalEntropy (b i))) := by
  let lam : ℕ → Fin (r + 1) → ℕ :=
    fun n => Weyl.flooredWeight b (n + 1)
  have hbase := Weyl.tendsto_log_dimension_div_log_two lam b hb hanti
    (fun n => Weyl.flooredWeight_antitone hanti.antitone (n + 1))
    (fun i => by
      simpa only [Weyl.flooredWeight, Nat.cast_add, Nat.cast_one, Function.comp_def, lam] using
        (tendsto_nat_floor_mul_atTop (b i) (hb i)).comp (tendsto_add_atTop_nat 1))
    (fun i => by
      simpa only [Weyl.flooredWeight, Nat.cast_add, Nat.cast_one, flooredCoordinates, lam] using
        tendsto_flooredCoordinates_succ_ratio b i (hb i).le)
  have hshift := hbase.comp (tendsto_sub_atTop_nat 1)
  have hratio := SpherePacking.tendsto_nat_sequence_sub_cast_div
    (fun n : ℕ => n) 1 1 tendsto_id
      SpherePacking.tendsto_natCast_div_self
  have hproduct := hshift.mul hratio
  have heq :
      (fun n : ℕ =>
        ((Real.log (Weyl.dimension (n - 1) (lam (n - 1))) /
            ((n - 1 : ℕ) : ℝ)) / Real.log 2) *
          (((n - 1 : ℕ) : ℝ) / (n : ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.log (Weyl.dimension (n - 1) (Weyl.flooredWeight b n)) /
          (n : ℝ)) / Real.log 2) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hpred : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show n - 1 ≠ 0 by omega)
    have hlog : Real.log 2 ≠ 0 :=
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    have hindex : n - 1 + 1 = n := by omega
    simp only [lam, hindex]
    field_simp
  simpa only [mul_one] using hproduct.congr' heq

end

section


open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherProjectionInstantiation

/-- Data encoding the indexed hierarchy graph construction. -/
structure IndexedHierarchyGraph (n : ℕ) where
  /-- The vertex count component. -/
  vertexCount : ℕ
  /-- The ambient dimension component. -/
  ambientDimension : ℕ
  /-- The fibre dimension component. -/
  fibreDimension : ℕ
  /-- The channel dimension component. -/
  channelDimension : ℕ
  /-- The graph component. -/
  graph : MetricCodes.HigherProjectionGraph.Data
    (Fin vertexCount) (SpherePoint n)
    ambientDimension fibreDimension channelDimension

theorem eventually_sphericalCode_card_lt_of_eventualGraphCertificates
    {s R gap : ℝ} (hs' : s < 1) (hgap : 0 < gap)
    (stable : ℕ → Prop)
    (hstable : ∀ᶠ n : ℕ in atTop, stable n)
    (G : (n : ℕ) → stable n → IndexedHierarchyGraph n)
    (hvertex : ∀ (n : ℕ) (h : stable n), 0 < (G n h).vertexCount)
    (hfibre : ∀ (n : ℕ) (h : stable n), 0 < (G n h).fibreDimension)
    (hcorrelation : ∀ (n : ℕ) (h : stable n) (x y : SpherePoint n),
      (G n h).graph.correlation x y =
        ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ)
    (heigenvalue : ∀ᶠ n : ℕ in atTop,
      ∀ h : stable n, s + gap < (G n h).graph.eigenvalue)
    (hdimension : ∀ᶠ n : ℕ in atTop,
      ∀ h : stable n,
        ((1 - s) / gap) *
            ((∑ k : Fin (G n h).vertexCount,
                ((G n h).graph.dimension k : ℝ)) /
              ((G n h).fibreDimension : ℝ)) <
          (2 : ℝ) ^ (R * (n : ℝ))) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ)) := by
  classical
  filter_upwards [hstable, heigenvalue, hdimension]
    with n hn heigen hrank
  intro C
  let H : IndexedHierarchyGraph n := G n hn
  have hHvertex : 0 < H.vertexCount := hvertex n hn
  have hHfibre : 0 < H.fibreDimension := hfibre n hn
  let : Nonempty (Fin H.vertexCount) :=
    Fin.pos_iff_nonempty.mp hHvertex
  have hfinite := sphericalCode_bound_of_realized_graph
    H.graph (hcorrelation n hn) hHfibre hs'
      (show s < H.graph.eigenvalue by
        change s < (G n hn).graph.eigenvalue
        linarith [heigen hn]) C
  have hfactor :
      (1 - s) / (H.graph.eigenvalue - s) ≤ (1 - s) / gap := by
    apply (div_le_div_iff₀ (by
      change 0 < (G n hn).graph.eigenvalue - s
      linarith [heigen hn]) hgap).mpr
    nlinarith [sub_pos.mpr hs', heigen hn]
  have hratio :
      0 ≤
        (∑ k : Fin H.vertexCount, (H.graph.dimension k : ℝ)) /
          (H.fibreDimension : ℝ) := by
    exact div_nonneg
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
      (Nat.cast_nonneg _)
  refine lt_of_le_of_lt ?_ (hrank hn)
  exact hfinite.trans (mul_le_mul_of_nonneg_right hfactor hratio)

theorem eventually_const_mul_lt_rpow_of_logRate
    {q : ℕ → ℝ} {L R K : ℝ}
    (hq : ∀ᶠ n : ℕ in atTop, 0 < q n)
    (hlim : Tendsto
      (fun n : ℕ => (Real.log (q n) / (n : ℝ)) / Real.log 2)
      atTop (nhds L))
    (hR : L < R) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, K * q n < (2 : ℝ) ^ (R * (n : ℝ)) := by
  have hconstant :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.log K)).div_const
      (Real.log 2)
  have hsum :
      Tendsto
        (fun n : ℕ =>
          (Real.log K / (n : ℝ)) / Real.log 2 +
            (Real.log (q n) / (n : ℝ)) / Real.log 2)
        atTop (nhds L) := by
    simpa only [zero_div, zero_add] using hconstant.add hlim
  have heq :
      (fun n : ℕ =>
        (Real.log K / (n : ℝ)) / Real.log 2 +
          (Real.log (q n) / (n : ℝ)) / Real.log 2) =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.log (K * q n) / (n : ℝ)) / Real.log 2) := by
    filter_upwards [hq] with n hn
    rw [Real.log_mul hK.ne' hn.ne']
    ring
  have hrate := (hsum.congr' heq).eventually (Iio_mem_nhds hR)
  filter_upwards [hrate, hq, eventually_gt_atTop (0 : ℕ)]
    with n hn hqn hnpos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpositive : 0 < K * q n := mul_pos hK hqn
  have hlog : Real.log (K * q n) < (R * Real.log 2) * (n : ℝ) :=
    (div_lt_iff₀ hnreal).mp ((div_lt_iff₀ hlogtwo).mp hn)
  calc
    K * q n = Real.exp (Real.log (K * q n)) :=
      (Real.exp_log hpositive).symm
    _ < Real.exp (Real.log 2 * (R * (n : ℝ))) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    _ = (2 : ℝ) ^ (R * (n : ℝ)) :=
      (Real.rpow_def_of_pos (by norm_num) _).symm

theorem eventually_const_mul_rectangularWeylQuotient_lt
    {r m : ℕ} {R K : ℝ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (h : Interlacing a b) (hlast : 0 < a (Fin.last (r + 1)))
    (hR : Phi a b < R) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop,
      K *
          (RectangularVertices.dimensionSum (m := m) a n /
            Weyl.dimension (n - 1)
              (Weyl.flooredWeight b n)) <
        (2 : ℝ) ^ (R * (n : ℝ)) := by
  have ha : ∀ i, 0 < a i := fun i =>
    hlast.trans_le (h.strictAnti_ambient.antitone i.le_last)
  have hb : ∀ i, 0 < b i := h.stabilizer_pos
  have hanti : StrictAnti a := h.strictAnti_ambient
  have hbanti : StrictAnti b := interlacing_strictAnti_stabilizer h
  have hpositive :
      ∀ᶠ n : ℕ in atTop,
        0 <
          RectangularVertices.dimensionSum (m := m) a n /
            Weyl.dimension (n - 1)
              (Weyl.flooredWeight b n) := by
    filter_upwards [RectangularVertices.eventually_vertexDimension_pos_all
      (m := m) a ha hanti, eventually_ge_atTop (2 * r + 5)]
      with n hn hstable
    apply div_pos
    · unfold RectangularVertices.dimensionSum
      apply Finset.sum_pos
      · intro i _
        exact hn i
      · exact Finset.univ_nonempty
    · apply Weyl.dimension_pos (by omega)
      exact Weyl.flooredWeight_antitone hbanti.antitone n
  have hlimit :
      Tendsto
        (fun n : ℕ =>
          (Real.log
            (RectangularVertices.dimensionSum (m := m) a n /
              Weyl.dimension (n - 1)
                (Weyl.flooredWeight b n)) /
            (n : ℝ)) / Real.log 2)
        atTop (nhds (Phi a b)) := by
    have hambient := RectangularVertices.tendsto_log_dimensionSum_div_log_two
      (m := m) a ha hanti
    have hstabilizer :=
      tendsto_log_stabilizerDimension_floor_current_div_log_two b hb hbanti
    have hdifference := hambient.sub hstabilizer
    apply hdifference.congr'
    filter_upwards [RectangularVertices.eventually_vertexDimension_pos_all
      (m := m) a ha hanti, eventually_ge_atTop (2 * r + 5)]
      with n hn hstable
    have hambientpos : 0 < RectangularVertices.dimensionSum (m := m) a n := by
      unfold RectangularVertices.dimensionSum
      exact Finset.sum_pos (fun i _ => hn i) Finset.univ_nonempty
    have hstabilizerpos :
        0 < Weyl.dimension (n - 1) (Weyl.flooredWeight b n) :=
      Weyl.dimension_pos (by omega)
        (Weyl.flooredWeight_antitone hbanti.antitone n)
    rw [Real.log_div hambientpos.ne' hstabilizerpos.ne']
    ring
  exact eventually_const_mul_lt_rpow_of_logRate hpositive hlimit hR hK

theorem fixedLevelHierarchyCodeBound_levelZero
    {s R : ℝ} (hs : 0 < s) (hs' : s < 1)
    (a : Fin 1 → ℝ) (b : Fin 0 → ℝ)
    (hinterlacing : Interlacing a b)
    (hspectral : s < 2 * Gamma a b)
    (hR : Phi a b < R) :
    ∀ᶠ n : ℕ in atTop, ∀ C : SpherePacking.SphericalCode n s,
      (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ)) := by
  filter_upwards [eventually_sphericalCode_card_lt_levelZero
    hs hs' a b hinterlacing hspectral, eventually_gt_atTop (0 : ℕ)]
    with n hn hnpos
  intro C
  refine (hn C).trans ?_
  apply Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  nlinarith [mul_pos (sub_pos.mpr hR) hnreal]

theorem fixedLevelHierarchyCodeBound_of_positiveTerminal
    (hpositive : ∀ {r : ℕ} {s R : ℝ}, 0 < s → s < 1 →
      ∀ (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
        Interlacing a b → 0 < a (Fin.last r) →
          s < 2 * Gamma a b → Phi a b < R →
            ∀ᶠ n : ℕ in atTop,
              ∀ C : SpherePacking.SphericalCode n s,
                (C.points.card : ℝ) < (2 : ℝ) ^ (R * (n : ℝ))) :
    FixedLevelHierarchyCodeBound := by
  intro r s R hs hs' a b hinterlacing hspectral hR
  by_cases hlast : 0 < a (Fin.last r)
  · exact hpositive hs hs' a b hinterlacing hlast hspectral hR
  · have hzero : a (Fin.last r) = 0 :=
      le_antisymm (le_of_not_gt hlast)
        (hinterlacing.ambient_nonneg (Fin.last r))
    cases r with
    | zero =>
        exact fixedLevelHierarchyCodeBound_levelZero
          hs hs' a b hinterlacing hspectral hR
    | succ r =>
        obtain ⟨A, hApos, hA, hGamma, hPhi⟩ :=
          exists_sameLevel_opening_strict_refinement
            (Nat.succ_pos r) hinterlacing hzero
        exact hpositive hs hs' A b hA hApos
          (by nlinarith) (by linarith)

theorem fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
    (hboxes : ∀ {r : ℕ} {s R : ℝ}, 0 < s → s < 1 →
      ∀ (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
        Interlacing a b → 0 < a (Fin.last (r + 1)) →
          s < 2 * Gamma a b → Phi a b < R →
            ∃ (m : ℕ) (gap : ℝ) (_ : 0 < gap)
              (stable : ℕ → Prop) (_ : DecidablePred stable)
              (_ : ∀ᶠ n : ℕ in atTop, stable n)
              (G : (n : ℕ) → stable n → IndexedHierarchyGraph n),
                (∀ (n : ℕ) (h : stable n), 0 < (G n h).vertexCount) ∧
                (∀ (n : ℕ) (h : stable n), 0 < (G n h).fibreDimension) ∧
                (∀ (n : ℕ) (h : stable n) (x y : SpherePoint n),
                  (G n h).graph.correlation x y =
                    ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ) ∧
                (∀ᶠ n : ℕ in atTop,
                  ∀ h : stable n,
                    s + gap < (G n h).graph.eigenvalue) ∧
                (∀ᶠ n : ℕ in atTop,
                  ∀ h : stable n,
                    (∑ i : Fin (G n h).vertexCount,
                        ((G n h).graph.dimension i : ℝ)) /
                      ((G n h).fibreDimension : ℝ) =
                      RectangularVertices.dimensionSum (m := m) a n /
                        Weyl.dimension (n - 1)
                          (Weyl.flooredWeight b n))) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_positiveTerminal
  intro r s R hs hs' a b hinterlacing hlast hspectral hR
  cases r with
  | zero =>
      exact fixedLevelHierarchyCodeBound_levelZero
        hs hs' a b hinterlacing hspectral hR
  | succ r =>
      obtain ⟨m, gap, hgap, stable, hdec, hstable, G,
          hvertex, hfibre, hcorrelation, heigenvalue, hrank⟩ :=
        hboxes hs hs' a b hinterlacing hlast hspectral hR
      let : DecidablePred stable := hdec
      have hK : 0 < (1 - s) / gap :=
        div_pos (sub_pos.mpr hs') hgap
      have hweyl := eventually_const_mul_rectangularWeylQuotient_lt
        (m := m) a b hinterlacing hlast hR hK
      have hdimension :
          ∀ᶠ n : ℕ in atTop,
            ∀ h : stable n,
              ((1 - s) / gap) *
                ((∑ i : Fin (G n h).vertexCount,
                    ((G n h).graph.dimension i : ℝ)) /
                  ((G n h).fibreDimension : ℝ)) <
                (2 : ℝ) ^ (R * (n : ℝ)) := by
        filter_upwards [hweyl, hrank] with n hn hnr h
        rw [hnr h]
        exact hn
      exact eventually_sphericalCode_card_lt_of_eventualGraphCertificates
        hs' hgap stable hstable G hvertex hfibre hcorrelation
        heigenvalue hdimension

end

end HigherHierarchy

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace HigherYoungActualGraphAssembly

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungGraphAssembly
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherProjectionInstantiation

/-- The young ambient used in the spherical-code argument. -/
abbrev YoungAmbient {I : Type*}
    {r : ℕ} (n : ℕ) (lam : I → Fin (r + 1) → ℕ) :=
  VertexAmbient (YoungVertex (n := n) lam)

/-- The young coordinate ambient used in the spherical-code argument. -/
abbrev YoungCoordinateAmbient {I : Type*}
    {r : ℕ} (n : ℕ) (lam : I → Fin (r + 1) → ℕ) :=
  SpherePacking.Euclidean n ⊗[ℝ] YoungAmbient n lam

private def coordinateInclusion {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ) (i : I) :
    (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam i) →ₗᵢ[ℝ]
      YoungCoordinateAmbient n lam :=
  TensorProduct.mapIsometry
    (LinearIsometryEquiv.refl ℝ
      (SpherePacking.Euclidean n)).toLinearIsometry
    (vertexInclusion (YoungVertex (n := n) lam) i)

@[simp] theorem coordinateInclusion_tmul
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ) (i : I)
    (x : SpherePacking.Euclidean n) (v : YoungVertex (n := n) lam i) :
    coordinateInclusion (n := n) lam i (x ⊗ₜ[ℝ] v) =
      x ⊗ₜ[ℝ] vertexInclusion (YoungVertex (n := n) lam) i v := rfl

theorem coordinateInclusion_orthogonal
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ)
    {i j : I} (hij : i ≠ j) :
    (coordinateInclusion (n := n) lam i).adjoint.comp
      (coordinateInclusion (n := n) lam j).toLinearMap = 0 := by
  apply LinearMap.ext
  intro t
  apply TensorProduct.ext_iff_inner_right.mpr
  intro x v
  rw [LinearMap.zero_apply, inner_zero_left]
  simp only [LinearMap.comp_apply]
  rw [LinearMap.adjoint_inner_left]
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearIsometry.coe_toLinearMap, map_zero, coordinateInclusion_tmul,
              inner_zero_left]
  | tmul y w =>
      change
        ⟪coordinateInclusion (n := n) lam j (y ⊗ₜ[ℝ] w),
          coordinateInclusion (n := n) lam i (x ⊗ₜ[ℝ] v)⟫_ℝ = 0
      rw [coordinateInclusion_tmul, coordinateInclusion_tmul,
        TensorProduct.inner_tmul]
      have hblock :
          ⟪vertexInclusion (YoungVertex (n := n) lam) i v,
            vertexInclusion (YoungVertex (n := n) lam) j w⟫_ℝ = 0 := by
        rw [PiLp.inner_apply]
        apply Finset.sum_eq_zero
        intro k _
        by_cases hki : k = i
        · subst k
          rw [vertexInclusion_apply_self,
            vertexInclusion_apply_ne (YoungVertex (n := n) lam) hij]
          exact inner_zero_right _
        · rw [vertexInclusion_apply_ne (YoungVertex (n := n) lam) hki]
          exact inner_zero_left _
      have hblock' :
          ⟪vertexInclusion (YoungVertex (n := n) lam) j w,
            vertexInclusion (YoungVertex (n := n) lam) i v⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact hblock
      rw [hblock', mul_zero]
  | add t s ht hs =>
      rw [map_add, inner_add_left, ht, hs, add_zero]

@[simp] theorem coordinateInclusion_adjoint_axis_self
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ) (i : I)
    (x : SpherePacking.Euclidean n) (v : YoungVertex (n := n) lam i) :
    (coordinateInclusion (n := n) lam i).adjoint
      (x ⊗ₜ[ℝ] vertexInclusion (YoungVertex (n := n) lam) i v) =
        x ⊗ₜ[ℝ] v := by
  rw [← coordinateInclusion_tmul]
  change
    ((coordinateInclusion (n := n) lam i).adjoint.comp
      (coordinateInclusion (n := n) lam i).toLinearMap) (x ⊗ₜ[ℝ] v) = _
  rw [(coordinateInclusion (n := n) lam i).adjoint_comp_self']
  rfl

@[simp] theorem coordinateInclusion_adjoint_axis_ne
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ)
    (i j : I) (hij : i ≠ j)
    (x : SpherePacking.Euclidean n) (v : YoungVertex (n := n) lam j) :
    (coordinateInclusion (n := n) lam i).adjoint
      (x ⊗ₜ[ℝ] vertexInclusion (YoungVertex (n := n) lam) j v) = 0 := by
  rw [← coordinateInclusion_tmul]
  change
    ((coordinateInclusion (n := n) lam i).adjoint.comp
      (coordinateInclusion (n := n) lam j).toLinearMap) (x ⊗ₜ[ℝ] v) = 0
  rw [coordinateInclusion_orthogonal lam hij]
  rfl

private def liftChannel {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ) (target source : I)
    (T : YoungVertex (n := n) lam source →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target)) :
    YoungAmbient n lam →ₗ[ℝ] YoungCoordinateAmbient n lam :=
  ((coordinateInclusion (n := n) lam target).toLinearMap.comp T.toLinearMap).comp
    (vertexInclusion (YoungVertex (n := n) lam) source).adjoint

theorem liftChannel_adjoint_comp_self
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ) (target source : I)
    (T : YoungVertex (n := n) lam source →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target)) :
    (liftChannel lam target source T).adjoint.comp
      (liftChannel lam target source T) =
        vertexProjection (YoungVertex (n := n) lam) source := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  change
    ⟪(liftChannel lam target source T).adjoint
        (liftChannel lam target source T v), w⟫_ℝ =
      ⟪vertexInclusion (YoungVertex (n := n) lam) source
        ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint v),
          w⟫_ℝ
  rw [LinearMap.adjoint_inner_left]
  calc
    ⟪liftChannel lam target source T v,
      liftChannel lam target source T w⟫_ℝ =
        ⟪(vertexInclusion (YoungVertex (n := n) lam) source).adjoint v,
          (vertexInclusion (YoungVertex (n := n) lam) source).adjoint w⟫_ℝ := by
            change
              ⟪coordinateInclusion (n := n) lam target
                  (T ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint v)),
                coordinateInclusion (n := n) lam target
                  (T ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint w))⟫_ℝ = _
            rw [(coordinateInclusion (n := n) lam target).inner_map_map,
              T.inner_map_map]
            rfl
    _ = ⟪vertexInclusion (YoungVertex (n := n) lam) source
          ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint v),
            w⟫_ℝ :=
            LinearMap.adjoint_inner_right
              (vertexInclusion (YoungVertex (n := n) lam) source).toLinearMap
                ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint v) w

theorem liftChannel_orthogonal_of_target_ne
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ)
    (target source target' source' : I)
    (T : YoungVertex (n := n) lam source →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target))
    (T' : YoungVertex (n := n) lam source' →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target'))
    (hne : target ≠ target') :
    (liftChannel lam target source T).adjoint.comp
      (liftChannel lam target' source' T') = 0 := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  rw [LinearMap.zero_apply, inner_zero_left]
  change
    ⟪(liftChannel lam target source T).adjoint
      (liftChannel lam target' source' T' v), w⟫_ℝ = 0
  rw [LinearMap.adjoint_inner_left]
  change
    ⟪coordinateInclusion (n := n) lam target'
        (T' ((vertexInclusion (YoungVertex (n := n) lam) source').adjoint v)),
      coordinateInclusion (n := n) lam target
        (T ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint w))⟫_ℝ = 0
  let z := T' ((vertexInclusion (YoungVertex (n := n) lam) source').adjoint v)
  let q := T ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint w)
  have hzero := congrArg
    (fun A : (SpherePacking.Euclidean n ⊗[ℝ]
      YoungVertex (n := n) lam target') →ₗ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          YoungVertex (n := n) lam target) => A z)
    (coordinateInclusion_orthogonal lam hne)
  change
    (coordinateInclusion (n := n) lam target).adjoint
      (coordinateInclusion (n := n) lam target' z) = 0 at hzero
  calc
    ⟪coordinateInclusion (n := n) lam target' z,
      coordinateInclusion (n := n) lam target q⟫_ℝ =
        ⟪(coordinateInclusion (n := n) lam target).adjoint
          (coordinateInclusion (n := n) lam target' z), q⟫_ℝ :=
            (LinearMap.adjoint_inner_left
              (coordinateInclusion (n := n) lam target).toLinearMap q
                (coordinateInclusion (n := n) lam target' z)).symm
    _ = 0 := by simp only [hzero, inner_zero_left]

theorem liftChannel_orthogonal_of_clebsch
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ)
    (target source source' : I)
    (T : YoungVertex (n := n) lam source →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target))
    (T' : YoungVertex (n := n) lam source' →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target))
    (horthogonal : T.adjoint.comp T'.toLinearMap = 0) :
    (liftChannel lam target source T).adjoint.comp
      (liftChannel lam target source' T') = 0 := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  rw [LinearMap.zero_apply, inner_zero_left]
  change
    ⟪(liftChannel lam target source T).adjoint
      (liftChannel lam target source' T' v), w⟫_ℝ = 0
  rw [LinearMap.adjoint_inner_left]
  change
    ⟪coordinateInclusion (n := n) lam target
        (T' ((vertexInclusion (YoungVertex (n := n) lam) source').adjoint v)),
      coordinateInclusion (n := n) lam target
        (T ((vertexInclusion (YoungVertex (n := n) lam) source).adjoint w))⟫_ℝ = 0
  rw [(coordinateInclusion (n := n) lam target).inner_map_map]
  let z := (vertexInclusion (YoungVertex (n := n) lam) source').adjoint v
  let q := (vertexInclusion (YoungVertex (n := n) lam) source).adjoint w
  have hzero := congrArg
    (fun A : YoungVertex (n := n) lam source' →ₗ[ℝ]
      YoungVertex (n := n) lam source => A z)
    horthogonal
  change T.adjoint (T' z) = 0 at hzero
  calc
    ⟪T' z, T q⟫_ℝ = ⟪T.adjoint (T' z), q⟫_ℝ :=
      (LinearMap.adjoint_inner_left T.toLinearMap q (T' z)).symm
    _ = 0 := by
      rw [hzero]
      exact inner_zero_left q

theorem liftChannel_adjoint_axis_self
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ)
    (target source : I)
    (T : YoungVertex (n := n) lam source →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target))
    (x : SpherePoint n) (v : YoungVertex (n := n) lam target) :
    (liftChannel lam target source T).adjoint
      (axisTensor x
        (vertexInclusion (YoungVertex (n := n) lam) target v)) =
      vertexInclusion (YoungVertex (n := n) lam) source
        (T.adjoint (x.val ⊗ₜ[ℝ] v)) := by
  unfold liftChannel
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint]
  change
    vertexInclusion (YoungVertex (n := n) lam) source
      (T.adjoint
        ((coordinateInclusion (n := n) lam target).adjoint
          (x.val ⊗ₜ[ℝ]
            vertexInclusion (YoungVertex (n := n) lam) target v))) = _
  rw [coordinateInclusion_adjoint_axis_self]

theorem liftChannel_adjoint_axis_ne
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ)
    (target source j : I)
    (T : YoungVertex (n := n) lam source →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ] YoungVertex (n := n) lam target))
    (h : target ≠ j)
    (x : SpherePoint n) (v : YoungVertex (n := n) lam j) :
    (liftChannel lam target source T).adjoint
      (axisTensor x
        (vertexInclusion (YoungVertex (n := n) lam) j v)) = 0 := by
  unfold liftChannel
  rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint]
  change
    vertexInclusion (YoungVertex (n := n) lam) source
      (T.adjoint
        ((coordinateInclusion (n := n) lam target).adjoint
          (x.val ⊗ₜ[ℝ]
            vertexInclusion (YoungVertex (n := n) lam) j v))) = 0
  rw [coordinateInclusion_adjoint_axis_ne lam target j h,
    map_zero, map_zero]

private def actualYoungChannel
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} (lam : I → Fin (r + 1) → ℕ)
    (probability : I → I → ℝ)
    (edge : (target source : I) → 0 < probability target source →
      YoungVertex (n := n) lam source →ₗᵢ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          YoungVertex (n := n) lam target))
    (target source : I) :
    YoungAmbient n lam →ₗ[ℝ] YoungCoordinateAmbient n lam :=
  if h : 0 < probability target source then
    liftChannel lam target source (edge target source h)
  else 0

private def actualYoungHilbertGraph
    {I : Type*} [Fintype I] [DecidableEq I]
    {r n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (lam : I → Fin (r + 1) → ℕ)
    (o : SpherePoint n)
    (base : (i : I) → E →ₗᵢ[ℝ] YoungVertex (n := n) lam i)
    (hfibre : 0 < Module.finrank ℝ E)
    (probability : I → I → ℝ)
    (hprobability : ∀ target source, 0 ≤ probability target source)
    (hbalance : ∀ target source,
      (Module.finrank ℝ (YoungVertex (n := n) lam target) : ℝ) *
          probability target source =
        (Module.finrank ℝ (YoungVertex (n := n) lam source) : ℝ) *
          probability source target)
    (edge : (target source : I) → 0 < probability target source →
      YoungVertex (n := n) lam source →ₗᵢ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          YoungVertex (n := n) lam target))
    (horthogonal : ∀ target source source'
      (h : 0 < probability target source)
      (h' : 0 < probability target source'),
        source ≠ source' →
          (edge target source h).adjoint.comp
            (edge target source' h').toLinearMap = 0)
    (hclebsch : ∀ target source
      (h : 0 < probability target source)
      (x : SpherePoint n) (v : E),
        (edge target source h).adjoint
          (x.val ⊗ₜ[ℝ]
            movingYoungFibre (lam target) o (base target) x v) =
          Real.sqrt (probability target source) •
            movingYoungFibre (lam source) o (base source) x v)
    (eigenvalue : ℝ) (heigenvalue : 0 < eigenvalue)
    (eigenvector : I → ℝ)
    (heigenvector : ∀ i, 0 < eigenvector i)
    (heigenvector_unit : (∑ i, eigenvector i ^ 2) = 1)
    (heigenvector_equation : ∀ i,
      (∑ j, Real.sqrt
        (probability i j * probability j i) * eigenvector j) =
          eigenvalue * eigenvector i) :
    RealizedHilbertGraph I (SpherePoint n) E
      (YoungAmbient n lam) (YoungCoordinateAmbient n lam) where
  dimension i := Module.finrank ℝ (YoungVertex (n := n) lam i)
  dimension_pos i := by
    have hle := LinearMap.finrank_le_finrank_of_injective
      (base i).injective
    omega
  block i := vertexProjection (YoungVertex (n := n) lam) i
  block_adjoint i := vertexProjection_adjoint _ i
  block_idempotent i := vertexProjection_idempotent _ i
  block_orthogonal i j h := vertexProjection_orthogonal _ h
  block_complete := sum_vertexProjection _
  block_trace i := trace_vertexProjection _ i
  fibre i x := movingYoungBlockFibre lam o base i x
  fibre_support i x := movingYoungBlockFibre_support lam o base i x
  correlation x y := ⟪(x.val : SpherePacking.Euclidean n), y.val⟫_ℝ
  axis x := axisTensor x
  axis_inner x y := axisTensor_adjoint_comp x y
  probability := probability
  probability_nonneg := hprobability
  balance := hbalance
  channel := actualYoungChannel lam probability edge
  channel_isometry target source := by
    by_cases h : 0 < probability target source
    · simp only [actualYoungChannel, dite_eq_left h, ite_eq_left h]
      exact liftChannel_adjoint_comp_self lam target source
        (edge target source h)
    · simp only [actualYoungChannel, h, ↓reduceDIte, map_zero, LinearMap.comp_zero, ↓reduceIte]
  channel_orthogonal target source target' source' hpair := by
    by_cases h : 0 < probability target source
    · by_cases h' : 0 < probability target' source'
      · simp only [actualYoungChannel, dite_eq_left h, dite_eq_left h']
        by_cases htarget : target = target'
        · subst target'
          have hsource : source ≠ source' := by
            intro heq
            apply hpair
            simp only [heq]
          exact liftChannel_orthogonal_of_clebsch lam target source source'
            (edge target source h) (edge target source' h')
            (horthogonal target source source' h h' hsource)
        · exact liftChannel_orthogonal_of_target_ne lam
            target source target' source'
            (edge target source h) (edge target' source' h') htarget
      · simp only [actualYoungChannel, h', ↓reduceDIte, LinearMap.comp_zero]
    · simp only [actualYoungChannel, h, ↓reduceDIte, map_zero, LinearMap.zero_comp]
  channel_axis target source j x := by
    by_cases hp : 0 < probability target source
    · simp only [actualYoungChannel, dite_eq_left hp]
      by_cases hj : target = j
      · subst j
        simp only []
        apply LinearMap.ext
        intro v
        change
          (liftChannel lam target source
            (edge target source hp)).adjoint
              (axisTensor x
                (vertexInclusion (YoungVertex (n := n) lam) target
                  (movingYoungFibre (lam target) o (base target) x v))) =
            Real.sqrt (probability target source) •
              vertexInclusion (YoungVertex (n := n) lam) source
                (movingYoungFibre (lam source) o (base source) x v)
        rw [liftChannel_adjoint_axis_self,
          hclebsch target source hp x v, map_smul]
      · simp only [ite_eq_right hj]
        apply LinearMap.ext
        intro v
        change
          (liftChannel lam target source
            (edge target source hp)).adjoint
              (axisTensor x
                (vertexInclusion (YoungVertex (n := n) lam) j
                  (movingYoungFibre (lam j) o (base j) x v))) = 0
        exact liftChannel_adjoint_axis_ne lam target source j
          (edge target source hp) hj x _
    · have hzero : probability target source = 0 :=
        le_antisymm (le_of_not_gt hp)
          (hprobability target source)
      simp only [actualYoungChannel, hzero, lt_self_iff_false, ↓reduceDIte, map_zero,
        LinearMap.zero_comp, Real.sqrt_zero, zero_smul, ite_self]
  eigenvalue := eigenvalue
  eigenvalue_pos := heigenvalue
  eigenvector := eigenvector
  eigenvector_pos := heigenvector
  eigenvector_unit := heigenvector_unit
  eigenvector_equation := heigenvector_equation

/-- The actual young indexed hierarchy graph used in the spherical-code argument. -/
def actualYoungIndexedHierarchyGraph
    {k r n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (lam : Fin k → Fin (r + 1) → ℕ)
    (G : RealizedHilbertGraph (Fin k) (SpherePoint n) E
      (YoungAmbient n lam) (YoungCoordinateAmbient n lam)) :
    MetricCodes.Spherical.HigherHierarchy.IndexedHierarchyGraph n where
  vertexCount := k
  ambientDimension := Module.finrank ℝ (YoungAmbient n lam)
  fibreDimension := Module.finrank ℝ E
  channelDimension := Module.finrank ℝ (YoungCoordinateAmbient n lam)
  graph := G.toFiniteData

/-- The box index used in the spherical-code argument. -/
abbrev BoxIndex (r m : ℕ) :=
  Fin (Fintype.card
    (MetricCodes.Spherical.HigherHierarchy.RectangularVertices.Vertex r m))

/-- The box signature used in the spherical-code argument. -/
def boxSignature {r m : ℕ} (a : Fin (r + 1) → ℝ) (n : ℕ)
    (i : BoxIndex r m) : Fin (r + 1) → ℕ :=
  MetricCodes.Spherical.HigherHierarchy.RectangularVertices.signature a n
    ((Fintype.equivFin
      (MetricCodes.Spherical.HigherHierarchy.RectangularVertices.Vertex
        r m)).symm i)

theorem sum_boxSignature_weyl
    {r m : ℕ} (a : Fin (r + 1) → ℝ) (n : ℕ) :
    (∑ i : BoxIndex r m,
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
        (boxSignature (m := m) a n i)) =
      MetricCodes.Spherical.HigherHierarchy.RectangularVertices.dimensionSum
        (m := m) a n := by
  classical
  unfold boxSignature
  unfold MetricCodes.Spherical.HigherHierarchy.RectangularVertices.dimensionSum
    MetricCodes.Spherical.HigherHierarchy.RectangularVertices.vertexDimension
  exact (Fintype.equivFin
    (MetricCodes.Spherical.HigherHierarchy.RectangularVertices.Vertex
      r m)).symm.sum_comp
        (fun v : MetricCodes.Spherical.HigherHierarchy.RectangularVertices.Vertex
          r m =>
            MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
              (MetricCodes.Spherical.HigherHierarchy.RectangularVertices.signature
                a n v))

theorem actualYoungBox_rankQuotient_eq_weyl
    {r m n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (G : RealizedHilbertGraph (BoxIndex (r + 1) m) (SpherePoint n) E
      (YoungAmbient n (boxSignature (m := m) a n))
      (YoungCoordinateAmbient n (boxSignature (m := m) a n)))
    (hdimension : ∀ i : BoxIndex (r + 1) m,
      G.dimension i = Module.finrank ℝ
        (YoungVertex (n := n) (boxSignature (m := m) a n) i))
    (hweyl : ∀ i : BoxIndex (r + 1) m,
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
        (boxSignature (m := m) a n i) =
        (Module.finrank ℝ
          (YoungVertex (n := n) (boxSignature (m := m) a n) i) : ℝ))
    (hfibre :
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension (n - 1)
        (MetricCodes.Spherical.HigherHierarchy.Weyl.flooredWeight b
          n) = (Module.finrank ℝ E : ℝ)) :
    ((∑ i : Fin
        (actualYoungIndexedHierarchyGraph
          (boxSignature (m := m) a n) G).vertexCount,
      ((actualYoungIndexedHierarchyGraph
        (boxSignature (m := m) a n) G).graph.dimension i : ℝ)) /
      ((actualYoungIndexedHierarchyGraph
        (boxSignature (m := m) a n) G).fibreDimension : ℝ)) =
      MetricCodes.Spherical.HigherHierarchy.RectangularVertices.dimensionSum
        (m := m) a n /
        MetricCodes.Spherical.HigherHierarchy.Weyl.dimension (n - 1)
          (MetricCodes.Spherical.HigherHierarchy.Weyl.flooredWeight b
            n) := by
  change
    (∑ i : BoxIndex (r + 1) m, (G.dimension i : ℝ)) /
        (Module.finrank ℝ E : ℝ) = _
  rw [← hfibre]
  congr 1
  calc
    (∑ i : BoxIndex (r + 1) m, (G.dimension i : ℝ)) =
        ∑ i : BoxIndex (r + 1) m,
          MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
            (boxSignature (m := m) a n i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdimension i, ← hweyl i]
    _ = _ := sum_boxSignature_weyl a n

end HigherYoungActualGraphAssembly

end

section


open Filter Topology
open scoped BigOperators InnerProductSpace Matrix TensorProduct Topology

namespace HigherHierarchyActualBoxSufficiency

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungMovingFibres

/-- The box stabilizer used in the spherical-code argument. -/
abbrev BoxStabilizer {r : ℕ} (n : ℕ) (b : Fin (r + 1) → ℝ) :=
  HarmonicYoungSpace (n := n - 1) (Weyl.flooredWeight b n)

/-- The box probability used in the spherical-code argument. -/
def boxProbability {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (target source : BoxIndex r m) : ℝ :=
  HigherHierarchyBoxChannels.probability a b n
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm source)

/-- Data encoding the box representation construction. -/
structure BoxRepresentationData {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ) where
  /-- The axis component. -/
  axis : SpherePoint n
  stabilizer_pos : 0 < Module.finrank ℝ (BoxStabilizer n b)
  stabilizer_weyl :
    Weyl.dimension (n - 1) (Weyl.flooredWeight b n) =
      (Module.finrank ℝ (BoxStabilizer n b) : ℝ)
  vertex_weyl : ∀ i : BoxIndex (r + 1) m,
    Weyl.dimension n (boxSignature (m := m) a n i) =
      (Module.finrank ℝ
        (YoungVertex (n := n) (boxSignature (m := m) a n) i) : ℝ)
  /-- The fibre component. -/
  fibre : (i : BoxIndex (r + 1) m) →
    BoxStabilizer n b →ₗᵢ[ℝ]
      YoungVertex (n := n) (boxSignature (m := m) a n) i
  /-- The edge component. -/
  edge : (target source : BoxIndex (r + 1) m) →
    0 < boxProbability a b n target source →
      YoungVertex (n := n) (boxSignature (m := m) a n) source →ₗᵢ[ℝ]
        (SpherePacking.Euclidean n ⊗[ℝ]
          YoungVertex (n := n) (boxSignature (m := m) a n) target)
  edge_orthogonal : ∀ target source source'
    (h : 0 < boxProbability a b n target source)
    (h' : 0 < boxProbability a b n target source'),
      source ≠ source' →
        (edge target source h).adjoint.comp
          (edge target source' h').toLinearMap = 0
  edge_axis : ∀ target source
    (h : 0 < boxProbability a b n target source)
    (x : SpherePoint n) (v : BoxStabilizer n b),
      (edge target source h).adjoint
          (x.val ⊗ₜ[ℝ]
            movingYoungFibre
              (boxSignature (m := m) a n target)
              axis (fibre target) x v) =
        Real.sqrt (boxProbability a b n target source) •
          movingYoungFibre
            (boxSignature (m := m) a n source)
            axis (fibre source) x v

theorem boxProbability_nonneg {r m n : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex r m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (target source : BoxIndex r m) :
    0 ≤ boxProbability (m := m) a b n target source := by
  exact HigherHierarchyBoxChannels.probability_nonneg a b n hstable
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm target)
    ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm source)

theorem BoxRepresentationData.detailed_balance {r m n : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (A : BoxRepresentationData (m := m) (n := n) a b)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (target source : BoxIndex (r + 1) m) :
    (Module.finrank ℝ
      (YoungVertex (n := n) (boxSignature (m := m) a n) target) : ℝ) *
        boxProbability a b n target source =
      (Module.finrank ℝ
        (YoungVertex (n := n) (boxSignature (m := m) a n) source) : ℝ) *
          boxProbability a b n source target := by
  rw [← A.vertex_weyl target, ← A.vertex_weyl source]
  exact HigherHierarchyBoxChannels.weyl_detailed_balance a b n hstable
    ((Fintype.equivFin
      (RectangularVertices.Vertex (r + 1) m)).symm target)
    ((Fintype.equivFin
      (RectangularVertices.Vertex (r + 1) m)).symm source)

private def indexedEigenvector {r m : ℕ}
    (x : RectangularVertices.Vertex r m → ℝ)
    (i : BoxIndex r m) : ℝ :=
  x ((Fintype.equivFin (RectangularVertices.Vertex r m)).symm i)

theorem indexedEigenvector_unit {r m : ℕ}
    (x : RectangularVertices.Vertex r m → ℝ)
    (hx : (∑ v, x v ^ 2) = 1) :
    (∑ i : BoxIndex r m, indexedEigenvector x i ^ 2) = 1 := by
  rw [← hx]
  exact (Fintype.equivFin (RectangularVertices.Vertex r m)).symm.sum_comp
    (fun v : RectangularVertices.Vertex r m => x v ^ 2)

theorem indexedEigenvector_equation {r m n : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (eigenvalue : ℝ)
    (x : RectangularVertices.Vertex r m → ℝ)
    (hx : ∀ v : RectangularVertices.Vertex r m,
      (∑ w : RectangularVertices.Vertex r m,
        HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n v w * x w) =
          eigenvalue * x v)
    (i : BoxIndex r m) :
    (∑ j : BoxIndex r m,
      Real.sqrt
        (boxProbability a b n i j * boxProbability a b n j i) *
          indexedEigenvector x j) =
      eigenvalue * indexedEigenvector x i := by
  let v : RectangularVertices.Vertex r m :=
    (Fintype.equivFin (RectangularVertices.Vertex r m)).symm i
  calc
    (∑ j : BoxIndex r m,
      Real.sqrt
        (boxProbability a b n i j * boxProbability a b n j i) *
          indexedEigenvector x j) =
        ∑ w : RectangularVertices.Vertex r m,
          Real.sqrt
            (HigherHierarchyBoxChannels.probability a b n v w *
              HigherHierarchyBoxChannels.probability a b n w v) * x w := by
      exact (Fintype.equivFin
        (RectangularVertices.Vertex r m)).symm.sum_comp
          (fun w : RectangularVertices.Vertex r m =>
            Real.sqrt
              (HigherHierarchyBoxChannels.probability a b n v w *
                HigherHierarchyBoxChannels.probability a b n w v) * x w)
    _ = ∑ w : RectangularVertices.Vertex r m,
        HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n v w *
          x w := by
      apply Finset.sum_congr rfl
      intro w _
      rw [HigherHierarchyBoxChannels.symmetric_probability_eq_trueGrid]
    _ = eigenvalue * indexedEigenvector x i := hx v

/-- Data encoding the box perron construction. -/
structure BoxPerronData {r m n : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (s gap : ℝ) where
  /-- The eigenvalue component. -/
  eigenvalue : ℝ
  /-- The eigenvector component. -/
  eigenvector : RectangularVertices.Vertex r m → ℝ
  spectral_gap : s + gap < eigenvalue
  positive : ∀ v : RectangularVertices.Vertex r m, 0 < eigenvector v
  unit : (∑ v : RectangularVertices.Vertex r m, eigenvector v ^ 2) = 1
  equation : ∀ v : RectangularVertices.Vertex r m,
    (∑ w : RectangularVertices.Vertex r m,
      HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n v w *
        eigenvector w) = eigenvalue * eigenvector v

/-- The to hilbert graph used in the spherical-code argument. -/
def BoxRepresentationData.toHilbertGraph {r m n : ℕ}
    {a : Fin (r + 2) → ℝ} {b : Fin (r + 1) → ℝ}
    (A : BoxRepresentationData (m := m) (n := n) a b)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing n (RectangularVertices.signature a n v)
        (flooredCoordinates b n))
    (eigenvalue : ℝ) (heigenvalue : 0 < eigenvalue)
    (x : RectangularVertices.Vertex (r + 1) m → ℝ)
    (hx : ∀ v, 0 < x v)
    (hunit : (∑ v, x v ^ 2) = 1)
    (hequation : ∀ v : RectangularVertices.Vertex (r + 1) m,
      (∑ w : RectangularVertices.Vertex (r + 1) m,
        HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n v w * x w) =
          eigenvalue * x v) :
    RealizedHilbertGraph
      (BoxIndex (r + 1) m) (SpherePoint n) (BoxStabilizer n b)
      (YoungAmbient n (boxSignature (m := m) a n))
      (YoungCoordinateAmbient n (boxSignature (m := m) a n)) :=
  actualYoungHilbertGraph (boxSignature (m := m) a n)
    A.axis A.fibre A.stabilizer_pos (boxProbability a b n)
    (boxProbability_nonneg a b hstable)
    (A.detailed_balance hstable)
    A.edge A.edge_orthogonal A.edge_axis
    eigenvalue heigenvalue (indexedEigenvector x)
    (fun i => hx
      ((Fintype.equivFin
        (RectangularVertices.Vertex (r + 1) m)).symm i))
    (indexedEigenvector_unit x hunit)
    (indexedEigenvector_equation a b eigenvalue x hequation)

end HigherHierarchyActualBoxSufficiency

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace AllRankClebschBranchCoherence

open MetricCodes.Spherical.HigherHarmonicYoung.FullRankClebschProbabilities
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem commonAxisReflection_base_to_moving_metriccodes2_17b3e1d2
    {n : ℕ} (o x : SpherePoint n) :
    AssociatedAxisTransport.commonAxisReflection o.val x.val o.val =
      x.val :=
  AssociatedAxisTransport.commonAxisReflection_apply_left
    o.val x.val o.property x.property

theorem projectedCoordinateRaise_movingFibre
    {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1))
    (o x : SpherePoint n)
    (base : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) lam)
    (v : E) :
    projectedCoordinateRaise mu lam hdeg row x.val
        (movingYoungFibre lam o base x v) =
      youngOrthogonalIsometry
        (AssociatedAxisTransport.commonAxisReflection o.val x.val) mu
        (projectedCoordinateRaise mu lam hdeg row o.val (base v)) := by
  change
    projectedCoordinateRaise mu lam hdeg row x.val
        (youngOrthogonalIsometry
          (AssociatedAxisTransport.commonAxisReflection o.val x.val)
          lam (base v)) = _
  simpa only [commonAxisReflection_base_to_moving_metriccodes2_17b3e1d2 o x] using
    (projectedCoordinateRaise_equivariant
      (AssociatedAxisTransport.commonAxisReflection o.val x.val)
      mu lam hdeg row o.val (base v))

theorem projectedCoordinateLower_movingFibre
    {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1))
    (o x : SpherePoint n)
    (base : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) lam)
    (v : E) :
    projectedCoordinateLower mu lam hdeg row x.val
        (movingYoungFibre lam o base x v) =
      youngOrthogonalIsometry
        (AssociatedAxisTransport.commonAxisReflection o.val x.val) mu
        (projectedCoordinateLower mu lam hdeg row o.val (base v)) := by
  change
    projectedCoordinateLower mu lam hdeg row x.val
        (youngOrthogonalIsometry
          (AssociatedAxisTransport.commonAxisReflection o.val x.val)
          lam (base v)) = _
  simpa only [commonAxisReflection_base_to_moving_metriccodes2_17b3e1d2 o x] using
    (projectedCoordinateLower_equivariant
      (AssociatedAxisTransport.commonAxisReflection o.val x.val)
      mu lam hdeg row o.val (base v))

theorem projectedCoordinateRaise_movingFibre_eq_smul
    {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, mu i) = (∑ i, lam i) + 1)
    (row : Fin (r + 1))
    (o : SpherePoint n)
    (source : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) lam)
    (target : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) mu)
    (c : ℝ)
    (hbase : ∀ v : E,
      projectedCoordinateRaise mu lam hdeg row o.val (source v) =
        c • target v)
    (x : SpherePoint n) (v : E) :
    projectedCoordinateRaise mu lam hdeg row x.val
        (movingYoungFibre lam o source x v) =
      c • movingYoungFibre mu o target x v := by
  rw [projectedCoordinateRaise_movingFibre, hbase]
  exact (youngOrthogonalIsometry
    (AssociatedAxisTransport.commonAxisReflection o.val x.val) mu).map_smul
      c (target v)

theorem projectedCoordinateLower_movingFibre_eq_smul
    {r n : ℕ}
    (mu lam : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, lam i) = (∑ i, mu i) + 1)
    (row : Fin (r + 1))
    (o : SpherePoint n)
    (source : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) lam)
    (target : E →ₗᵢ[ℝ] HarmonicYoungSpace (n := n) mu)
    (c : ℝ)
    (hbase : ∀ v : E,
      projectedCoordinateLower mu lam hdeg row o.val (source v) =
        c • target v)
    (x : SpherePoint n) (v : E) :
    projectedCoordinateLower mu lam hdeg row x.val
        (movingYoungFibre lam o source x v) =
      c • movingYoungFibre mu o target x v := by
  rw [projectedCoordinateLower_movingFibre, hbase]
  exact (youngOrthogonalIsometry
    (AssociatedAxisTransport.commonAxisReflection o.val x.val) mu).map_smul
      c (target v)

end AllRankClebschBranchCoherence

end

section


open scoped BigOperators InnerProductSpace

namespace AllRankArbitraryRowBranchingOperator

open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
open MetricCodes.Spherical.HigherYoungProjectedRaiseInjectivity

/-- The preceding rows used in the spherical-code argument. -/
def precedingRows {r : ℕ} (row : Fin (r + 1)) : Finset (Fin (r + 1)) :=
  Finset.univ.filter (fun i => i < row)

@[simp] theorem mem_precedingRows {r : ℕ}
    (i row : Fin (r + 1)) : i ∈ precedingRows row ↔ i < row := by
  simp only [precedingRows, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The shifted row gap used in the spherical-code argument. -/
def shiftedRowGap {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row i : Fin (r + 1)) : ℝ :=
  ((lam i - lam row : ℕ) : ℝ) +
    ((row.val - i.val - 1 : ℕ) : ℝ)

/-- The arbitrary row leading scalar used in the spherical-code argument. -/
def arbitraryRowLeadingScalar {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) : ℝ :=
  ∏ i ∈ precedingRows row, shiftedRowGap lam row i

/-- The lower polarization path used in the spherical-code argument. -/
def lowerPolarizationPath {r n : ℕ} :
    List (Fin (r + 1)) →
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
  | [] => LinearMap.id
  | [_] => LinearMap.id
  | i :: j :: rest =>
      (polarization r n j i).comp
        (lowerPolarizationPath (j :: rest))

/-- The polarization path start used in the spherical-code argument. -/
def polarizationPathStart {r : ℕ}
    (row : Fin (r + 1)) (S : Finset (Fin (r + 1))) : Fin (r + 1) :=
  if h : S.Nonempty then S.min' h else row

/-- The polarization path coefficient used in the spherical-code argument. -/
def polarizationPathCoefficient {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (S : Finset (Fin (r + 1))) : ℝ :=
  (-1 : ℝ) ^ S.card *
    ∏ i ∈ precedingRows row \ S, shiftedRowGap lam row i

/-- The arbitrary row axial raise used in the spherical-code argument. -/
def arbitraryRowAxialRaise {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) (k : Fin n) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  ∑ S ∈ (precedingRows row).powerset,
    polarizationPathCoefficient lam row S •
      ((LinearMap.mulLeft ℝ
        (MvPolynomial.X
          (variableIndex (polarizationPathStart row S) k))).comp
        (lowerPolarizationPath
          ((S.sort (· ≤ ·)) ++ [row])))

@[simp] theorem arbitraryRowAxialRaise_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    arbitraryRowAxialRaise lam row k p =
      ∑ S ∈ (precedingRows row).powerset,
        polarizationPathCoefficient lam row S •
          (MvPolynomial.X
            (variableIndex (polarizationPathStart row S) k) *
            lowerPolarizationPath
              ((S.sort (· ≤ ·)) ++ [row]) p) := by
  simp only [arbitraryRowAxialRaise, LinearMap.coe_sum, LinearMap.coe_smul, LinearMap.coe_comp,
    Finset.sum_apply, Pi.smul_apply, Function.comp_apply, LinearMap.mulLeft_apply]

@[simp] theorem polarizationPathStart_empty {r : ℕ}
    (row : Fin (r + 1)) :
    polarizationPathStart row ∅ = row := by
  simp only [polarizationPathStart, Finset.not_nonempty_empty, ↓reduceDIte]

theorem polarizationPathStart_lt_of_nonempty {r : ℕ}
    (row : Fin (r + 1)) (S : Finset (Fin (r + 1)))
    (hS : S.Nonempty) (hsub : S ⊆ precedingRows row) :
    polarizationPathStart row S < row := by
  rw [polarizationPathStart, dite_eq_left hS]
  exact (mem_precedingRows _ _).mp
    (hsub (Finset.min'_mem S hS))

theorem shiftedRowGap_pos
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (row i : Fin (r + 1)) (hi : i < row)
    (hstrict : ∀ j : Fin (r + 1),
      j.val + 1 = row.val → lam row < lam j) :
    0 < shiftedRowGap lam row i := by
  by_cases hadj : i.val + 1 = row.val
  · have hgap : 0 < lam i - lam row :=
      Nat.sub_pos_of_lt (hstrict i hadj)
    unfold shiftedRowGap
    exact add_pos_of_pos_of_nonneg (by exact_mod_cast hgap)
      (by positivity)
  · have hshift : 0 < row.val - i.val - 1 := by
      have hil : i.val < row.val := hi
      omega
    unfold shiftedRowGap
    exact add_pos_of_nonneg_of_pos (by positivity)
      (by exact_mod_cast hshift)

theorem arbitraryRowLeadingScalar_pos
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1))
    (hstrict : ∀ j : Fin (r + 1),
      j.val + 1 = row.val → lam row < lam j) :
    0 < arbitraryRowLeadingScalar lam row := by
  unfold arbitraryRowLeadingScalar
  apply Finset.prod_pos
  intro i hi
  exact shiftedRowGap_pos lam row i
    ((mem_precedingRows i row).mp hi) hstrict

end AllRankArbitraryRowBranchingOperator

end

end HigherHarmonicYoung

section


open scoped BigOperators

namespace HigherYoungArbitraryRankInterlacingGapSchedule

open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.ThreeRowYoungBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

/-- The interlacing gap used in the spherical-code argument. -/
def interlacingGap {r : ℕ}
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2)) : ℕ :=
  lam row - appendZeroWeight mu row

theorem appendZeroWeight_le_of_interlaces {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) (row : Fin (r + 2)) :
    appendZeroWeight mu row ≤ lam row := by
  induction row using Fin.lastCases with
  | last => simp only [appendZeroWeight_last, zero_le]
  | cast i => simpa only [appendZeroWeight_castSucc] using (h i).1

theorem appendZeroWeight_add_interlacingGap {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) (row : Fin (r + 2)) :
    appendZeroWeight mu row + interlacingGap lam mu row = lam row := by
  unfold interlacingGap
  exact Nat.add_sub_of_le (appendZeroWeight_le_of_interlaces h row)

theorem interlaces_of_between_appendZero_and_target {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) (theta : Fin (r + 2) → ℕ)
    (hlower : ∀ row, appendZeroWeight mu row ≤ theta row)
    (hupper : ∀ row, theta row ≤ lam row) :
    Interlaces theta mu := by
  intro i
  constructor
  · simpa only [appendZeroWeight_castSucc] using hlower i.castSucc
  · exact (hupper i.succ).trans (h i).2

/-- The interlacing row schedule used in the spherical-code argument. -/
def interlacingRowSchedule {r : ℕ}
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ) :
    List (Fin (r + 2)) :=
  (List.finRange (r + 2)).flatMap fun row =>
    List.replicate (interlacingGap lam mu row) row

theorem foldl_raiseWeight_apply {r : ℕ}
    (rows : List (Fin (r + 2))) (weight : Fin (r + 2) → ℕ)
    (row : Fin (r + 2)) :
    (rows.foldl (fun w i => raiseWeight w i) weight) row =
      weight row + rows.count row := by
  classical
  induction rows generalizing weight with
  | nil => simp only [List.foldl_nil, List.count_nil, add_zero]
  | cons i rows ih =>
      rw [List.foldl_cons, ih]
      by_cases hi : i = row
      · subst i
        simp only [raiseWeight, Function.update_self, List.count_cons_self]
        omega
      · have hri : row ≠ i := Ne.symm hi
        simp only [raiseWeight, ne_eq, hri, not_false_eq_true, Function.update_of_ne, hi,
          List.count_cons_of_ne]

theorem interlacingRowSchedule_count {r : ℕ}
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2)) :
    (interlacingRowSchedule lam mu).count row =
      interlacingGap lam mu row := by
  classical
  have hgeneral (l : List (Fin (r + 2))) (hl : l.Nodup)
      (f : Fin (r + 2) → ℕ) (i : Fin (r + 2)) :
      (l.flatMap fun j => List.replicate (f j) j).count i =
        if i ∈ l then f i else 0 := by
    induction l with
    | nil => simp only [List.flatMap_nil, List.count_nil, List.not_mem_nil,
               ↓reduceIte]
    | cons j tail ih =>
        have hnodup := (List.nodup_cons.mp hl)
        rw [List.flatMap_cons, List.count_append, ih hnodup.2]
        by_cases hji : j = i
        · subst j
          simp only [List.count_replicate_self, hnodup.1, ↓reduceIte, add_zero, List.mem_cons,
            or_false]
        · have hij : i ≠ j := Ne.symm hji
          simp only [List.count_replicate, beq_iff_eq, hji, ↓reduceIte, zero_add, List.mem_cons,
            hij, false_or]
  simpa only [interlacingRowSchedule, List.mem_finRange, ↓reduceIte] using
    hgeneral (List.finRange (r + 2)) (List.nodup_finRange (r + 2)) (interlacingGap lam mu) row

end HigherYoungArbitraryRankInterlacingGapSchedule

namespace HigherYoungArbitraryRankInterlacingLegalSchedule

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem foldl_interlaces_of_count_le_gap {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) (rows : List (Fin (r + 2)))
    (hrows : ∀ row, rows.count row ≤ interlacingGap lam mu row) :
    Interlaces
      (rows.foldl (fun weight row => raiseWeight weight row)
        (appendZeroWeight mu)) mu := by
  apply interlaces_of_between_appendZero_and_target h
    (rows.foldl (fun weight row => raiseWeight weight row)
      (appendZeroWeight mu))
  · intro row
    rw [foldl_raiseWeight_apply]
    omega
  · intro row
    rw [foldl_raiseWeight_apply]
    have hgap := appendZeroWeight_add_interlacingGap h row
    have hcount := hrows row
    omega

theorem foldl_strict_predecessor_of_count_lt_gap {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) (rows : List (Fin (r + 2)))
    (hrows : ∀ row, rows.count row ≤ interlacingGap lam mu row)
    (row j : Fin (r + 2))
    (hrow : rows.count row < interlacingGap lam mu row)
    (hj : j.val + 1 = row.val) :
    (rows.foldl (fun weight i => raiseWeight weight i)
        (appendZeroWeight mu)) row <
      (rows.foldl (fun weight i => raiseWeight weight i)
        (appendZeroWeight mu)) j := by
  let theta : Fin (r + 2) → ℕ :=
    rows.foldl (fun weight i => raiseWeight weight i)
      (appendZeroWeight mu)
  have htheta := foldl_interlaces_of_count_le_gap h rows hrows
  have hval : row.val ≠ 0 := by omega
  let i : Fin (r + 1) :=
    ⟨j.val, by have hjlt := j.isLt; omega⟩
  have hjcast : i.castSucc = j := Fin.ext rfl
  have hisucc : i.succ = row := Fin.ext hj
  have hgap := appendZeroWeight_add_interlacingGap h row
  have hcount := foldl_raiseWeight_apply rows (appendZeroWeight mu) row
  have htheta_lt : theta row < lam row := by
    change (rows.foldl (fun weight i => raiseWeight weight i)
      (appendZeroWeight mu)) row < lam row
    omega
  have htarget : lam row ≤ mu i := by
    simpa only [hisucc] using (h i).2
  have hpreceding : mu i ≤ theta j := by
    simpa only [hjcast] using (htheta i).1
  exact htheta_lt.trans_le (htarget.trans hpreceding)

theorem foldl_arbitraryRowLeadingScalar_pos_of_count_lt_gap {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) (rows : List (Fin (r + 2)))
    (hrows : ∀ row, rows.count row ≤ interlacingGap lam mu row)
    (row : Fin (r + 2))
    (hrow : rows.count row < interlacingGap lam mu row) :
    0 < arbitraryRowLeadingScalar
      (rows.foldl (fun weight i => raiseWeight weight i)
        (appendZeroWeight mu)) row := by
  apply arbitraryRowLeadingScalar_pos
  intro j hj
  exact foldl_strict_predecessor_of_count_lt_gap h rows hrows
    row j hrow hj

/-- The reverse interlacing row schedule used in the spherical-code argument. -/
def reverseInterlacingRowSchedule {r : ℕ}
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ) :
    List (Fin (r + 2)) :=
  (interlacingRowSchedule lam mu).reverse

theorem reverseInterlacingRowSchedule_count {r : ℕ}
    (lam : Fin (r + 2) → ℕ) (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 2)) :
    (reverseInterlacingRowSchedule lam mu).count row =
      interlacingGap lam mu row := by
  rw [reverseInterlacingRowSchedule, List.count_reverse]
  exact interlacingRowSchedule_count lam mu row

theorem foldl_reverseInterlacingRowSchedule_eq_target {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) :
    (reverseInterlacingRowSchedule lam mu).foldl
      (fun weight row => raiseWeight weight row)
      (appendZeroWeight mu) = lam := by
  funext row
  rw [foldl_raiseWeight_apply,
    reverseInterlacingRowSchedule_count,
    appendZeroWeight_add_interlacingGap h row]

end HigherYoungArbitraryRankInterlacingLegalSchedule

namespace HigherYoungSameAxisCoefficient

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

end HigherYoungSameAxisCoefficient

end

namespace HigherHarmonicYoung

section


open scoped BigOperators

theorem polarization_rowPairingPolynomial {r n : ℕ}
    (i j a b : Fin (r + 1)) :
    polarization r n i j
        (rowPairingPolynomial (r := r) (n := n) a b) =
      (if j = a then rowPairingPolynomial (r := r) (n := n) i b else 0) +
        (if j = b then rowPairingPolynomial (r := r) (n := n) a i else 0) := by
  classical
  unfold rowPairingPolynomial
  rw [map_sum]
  simp_rw [polarization_mul_euler, polarization_X_euler]
  by_cases hja : j = a
  · subst a
    by_cases hjb : j = b
    · subst b
      simp only [↓reduceIte, Finset.sum_add_distrib]
    · simp only [↓reduceIte, hjb, mul_zero, add_zero]
  · by_cases hjb : j = b
    · subst b
      simp only [hja, ↓reduceIte, zero_mul, zero_add]
    · simp only [hja, ↓reduceIte, zero_mul, hjb, mul_zero, add_zero, Finset.sum_const_zero]

namespace ArbitraryRankMixedTraceRegularity

open MetricCodes.Spherical.HigherHarmonicYoung

/-- The upper gram pair used in the spherical-code argument. -/
abbrev UpperGramPair (r : ℕ) :=
  {z : Fin (r + 1) × Fin (r + 1) // z.1 ≤ z.2}

/-- The gram pair polynomial used in the spherical-code argument. -/
def gramPairPolynomial {r : ℕ} (n : ℕ)
    (z : UpperGramPair r) : PolynomialSpace r n :=
  rowPairingPolynomial (n := n) z.val.1 z.val.2

/-- The gram quadratic list used in the spherical-code argument. -/
def gramQuadraticList (r n : ℕ) : List (PolynomialSpace r n) :=
  (Finset.univ : Finset (UpperGramPair r)).toList.map
    (gramPairPolynomial n)

/-- The gram prior ideal used in the spherical-code argument. -/
def gramPriorIdeal (r n k : ℕ) : Ideal (PolynomialSpace r n) :=
  Ideal.ofList ((gramQuadraticList r n).take k)

theorem mem_ideal_smul_top_iff {R : Type*} [CommRing R]
    (I : Ideal R) (p : R) :
    p ∈ (I • (⊤ : Submodule R R) : Submodule R R) ↔ p ∈ I := by
  rw [Ideal.smul_top_eq_map]
  simpa only using (show p ∈ Submodule.restrictScalars R (Ideal.map (algebraMap R R) I) ↔ p ∈ I
    by simp)

theorem gramQuadraticList_weaklyRegular_iff_saturation
    (r n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (PolynomialSpace r n)
        (gramQuadraticList r n) ↔
      ∀ k : Fin (gramQuadraticList r n).length,
        ∀ p : PolynomialSpace r n,
          (gramQuadraticList r n)[k] * p ∈
              gramPriorIdeal r n k.val →
            p ∈ gramPriorIdeal r n k.val := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff_Fin]
  apply forall_congr'
  intro k
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  constructor
  · intro h p hp
    apply (mem_ideal_smul_top_iff _ p).mp
    apply h p
    apply (mem_ideal_smul_top_iff _ _).mpr
    simpa only [Fin.getElem_fin, smul_eq_mul, gramPriorIdeal] using hp
  · intro h p hp
    apply (mem_ideal_smul_top_iff _ p).mpr
    apply h p
    apply (mem_ideal_smul_top_iff _ _).mp
    simpa only [gramPriorIdeal, smul_eq_mul, Ideal.mul_top, Fin.getElem_fin] using hp

/-- The gram pivot used in the spherical-code argument. -/
def gramPivot {r n : ℕ} (hn : 2 * r < n)
    (z : UpperGramPair r) : Fin n :=
  ⟨z.val.1.val + z.val.2.val, by
    have hi := z.val.1.isLt
    have hj := z.val.2.isLt
    omega⟩

@[simp] theorem gramPivot_val {r n : ℕ} (hn : 2 * r < n)
    (z : UpperGramPair r) :
    (gramPivot hn z).val = z.val.1.val + z.val.2.val := rfl

/-- The gram pivot variables used in the spherical-code argument. -/
def gramPivotVariables {r n : ℕ} (hn : 2 * r < n)
    (z : UpperGramPair r) : Finset (Fin ((r + 1) * n)) :=
  {variableIndex z.val.1 (gramPivot hn z),
    variableIndex z.val.2 (gramPivot hn z)}

theorem gramPivot_pair_eq_of_variable_eq {r n : ℕ}
    (hn : 2 * r < n) (z w : UpperGramPair r)
    (a b : Fin (r + 1))
    (ha : a = z.val.1 ∨ a = z.val.2)
    (hb : b = w.val.1 ∨ b = w.val.2)
    (h : variableIndex a (gramPivot hn z) =
      variableIndex b (gramPivot hn w)) :
    z = w := by
  have hindex := (variableIndex_eq_iff_harmonicLift
    a b (gramPivot hn z) (gramPivot hn w)).mp h
  have hrow := congrArg Fin.val hindex.1
  have hcolumn := congrArg Fin.val hindex.2
  have hz := z.property
  have hw := w.property
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [gramPivot_val] at hcolumn <;> omega
  · apply Fin.ext
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [gramPivot_val] at hcolumn <;> omega

theorem gramPivotVariables_disjoint {r n : ℕ}
    (hn : 2 * r < n) (z w : UpperGramPair r) (hzw : z ≠ w) :
    Disjoint (gramPivotVariables hn z) (gramPivotVariables hn w) := by
  apply Finset.disjoint_left.mpr
  intro a haz haw
  simp only [gramPivotVariables, Finset.mem_insert,
    Finset.mem_singleton] at haz haw
  rcases haz with hza | hza <;> rcases haw with hwa | hwa
  · exact hzw (gramPivot_pair_eq_of_variable_eq hn z w
      z.val.1 w.val.1 (Or.inl rfl) (Or.inl rfl)
      (hza.symm.trans hwa))
  · exact hzw (gramPivot_pair_eq_of_variable_eq hn z w
      z.val.1 w.val.2 (Or.inl rfl) (Or.inr rfl)
      (hza.symm.trans hwa))
  · exact hzw (gramPivot_pair_eq_of_variable_eq hn z w
      z.val.2 w.val.1 (Or.inr rfl) (Or.inl rfl)
      (hza.symm.trans hwa))
  · exact hzw (gramPivot_pair_eq_of_variable_eq hn z w
      z.val.2 w.val.2 (Or.inr rfl) (Or.inr rfl)
      (hza.symm.trans hwa))

/-- The gram pivot exponent used in the spherical-code argument. -/
def gramPivotExponent {r n : ℕ} (hn : 2 * r < n)
    (z : UpperGramPair r) : Fin ((r + 1) * n) →₀ ℕ :=
  Finsupp.single (variableIndex z.val.1 (gramPivot hn z)) 1 +
    Finsupp.single (variableIndex z.val.2 (gramPivot hn z)) 1

private def gramSummandExponent {r n : ℕ}
    (z : UpperGramPair r) (k : Fin n) :
    Fin ((r + 1) * n) →₀ ℕ :=
  Finsupp.single (variableIndex z.val.1 k) 1 +
    Finsupp.single (variableIndex z.val.2 k) 1

theorem gramSummandExponent_support {r n : ℕ}
    (z : UpperGramPair r) (k : Fin n) :
    (gramSummandExponent z k).support =
      {variableIndex z.val.1 k, variableIndex z.val.2 k} := by
  classical
  ext a
  by_cases h₁ : a = variableIndex z.val.1 k <;>
    by_cases h₂ : a = variableIndex z.val.2 k <;>
      simp [gramSummandExponent, Finsupp.mem_support_iff, h₁, h₂]

theorem gramPivotExponent_support {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r) :
    (gramPivotExponent hn z).support = gramPivotVariables hn z := by
  classical
  simpa only [gramPivotExponent, gramPivotVariables, gramSummandExponent] using
    gramSummandExponent_support z (gramPivot hn z)

theorem gramPivotExponent_support_disjoint {r n : ℕ}
    (hn : 2 * r < n) (z w : UpperGramPair r) (hzw : z ≠ w) :
    Disjoint (gramPivotExponent hn z).support
      (gramPivotExponent hn w).support := by
  simpa only [gramPivotExponent_support] using gramPivotVariables_disjoint hn z w hzw

theorem gramSummandExponent_eq_pivot_iff {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r) (k : Fin n) :
    gramSummandExponent z k = gramPivotExponent hn z ↔
      k = gramPivot hn z := by
  constructor
  · intro h
    by_contra hk
    have hcoeff := congrArg
      (fun d : Fin ((r + 1) * n) →₀ ℕ =>
        d (variableIndex z.val.1 (gramPivot hn z))) h
    by_cases hz : z.val.2 = z.val.1
    · simp only [gramSummandExponent, hz, Finsupp.coe_add, Pi.add_apply, ne_eq,
        variableIndex_eq_iff_harmonicLift, Ne.symm hk, and_false, not_false_eq_true,
        Finsupp.single_eq_of_ne, add_zero, gramPivotExponent, Finsupp.single_eq_same, Nat.reduceAdd,
        OfNat.zero_ne_ofNat] at hcoeff
    · simp only [gramSummandExponent, Finsupp.coe_add, Pi.add_apply, ne_eq,
        variableIndex_eq_iff_harmonicLift, Ne.symm hk, and_false, not_false_eq_true,
        Finsupp.single_eq_of_ne, add_zero, gramPivotExponent, Finsupp.single_eq_same, hz, and_true,
        Finsupp.single_eq_of_ne', zero_ne_one] at hcoeff
  · rintro rfl
    rfl

theorem coeff_gramPairPolynomial_pivot {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r) :
    MvPolynomial.coeff (gramPivotExponent hn z)
      (gramPairPolynomial n z) = 1 := by
  classical
  unfold gramPairPolynomial rowPairingPolynomial
  simp only [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (gramPivot hn z)]
  · simp only [gramPivotExponent, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one,
      MvPolynomial.coeff_monomial, ↓reduceIte]
  · intro k _ hk
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul,
      MvPolynomial.coeff_monomial, ite_eq_right_iff, ]
    simpa only [gramPivotExponent, mul_one, one_ne_zero, imp_false, gramSummandExponent, ne_eq]
      using
      (show gramSummandExponent z k ≠ gramPivotExponent hn z from fun h =>
        hk ((gramSummandExponent_eq_pivot_iff hn z k).mp h))
  · simp only [Finset.mem_univ, not_true_eq_false, IsEmpty.forall_iff]

private def gramVariableWeight (r n : ℕ)
    (i : Fin (r + 1)) (k : Fin n) : ℤ :=
  ((n + 2 * r : ℕ) : ℤ) ^ 2 -
    ((k.val : ℤ) - 2 * (i.val : ℤ)) ^ 2

private def gramSummandWeight {r n : ℕ}
    (z : UpperGramPair r) (k : Fin n) : ℤ :=
  gramVariableWeight r n z.val.1 k +
    gramVariableWeight r n z.val.2 k

theorem gramPivot_weight_sub {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r) (k : Fin n) :
    gramSummandWeight z (gramPivot hn z) - gramSummandWeight z k =
      2 * ((k.val : ℤ) -
        ((z.val.1.val : ℤ) + (z.val.2.val : ℤ))) ^ 2 := by
  unfold gramSummandWeight gramVariableWeight
  simp only [gramPivot_val, Nat.cast_add]
  ring

theorem gramPivot_unique_max_weight {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r)
    (k : Fin n) (hk : k ≠ gramPivot hn z) :
    gramSummandWeight z k < gramSummandWeight z (gramPivot hn z) := by
  have hne : (k.val : ℤ) ≠
      ((z.val.1.val : ℤ) + (z.val.2.val : ℤ)) := by
    intro h
    apply hk
    apply Fin.ext
    exact_mod_cast h
  have hpositive :
      0 < 2 * ((k.val : ℤ) -
        ((z.val.1.val : ℤ) + (z.val.2.val : ℤ))) ^ 2 := by
    positivity
  linarith [gramPivot_weight_sub hn z k]

end ArbitraryRankMixedTraceRegularity

end

section


open Finsupp
open scoped MonomialOrder

private def YoungWeightedLex {σ : Type*} (_w : σ → ℕ) := σ →₀ ℕ

private def toYoungWeightedLex {σ : Type*} (w : σ → ℕ) :
    (σ →₀ ℕ) ≃ YoungWeightedLex w := Equiv.refl _

private def ofYoungWeightedLex {σ : Type*} (w : σ → ℕ) :
    YoungWeightedLex w ≃ (σ →₀ ℕ) := Equiv.refl _

namespace YoungWeightedLex

variable {σ : Type*} (w : σ → ℕ)

noncomputable instance : AddCommMonoid (YoungWeightedLex w) :=
  (ofYoungWeightedLex w).addCommMonoid

@[simp] theorem toYoungWeightedLex_add (a b : σ →₀ ℕ) :
    toYoungWeightedLex w (a + b) =
      toYoungWeightedLex w a + toYoungWeightedLex w b := rfl

@[simp] theorem ofYoungWeightedLex_add (a b : YoungWeightedLex w) :
    ofYoungWeightedLex w (a + b) =
      ofYoungWeightedLex w a + ofYoungWeightedLex w b := rfl

section LinearOrder

variable [LinearOrder σ]

private def key_metriccodes2_a7f44027 (a : YoungWeightedLex w) : Lex (ℕ × Lex (σ →₀ ℕ)) :=
  toLex ((Finsupp.weight w) (ofYoungWeightedLex w a),
    toLex (ofYoungWeightedLex w a))

omit [LinearOrder σ] in
private theorem key_injective_metriccodes2_a7f44027 : Function.Injective
  (key_metriccodes2_a7f44027 w) := by
  intro a b hab
  have h := congrArg (fun z : Lex (ℕ × Lex (σ →₀ ℕ)) =>
    (ofLex z).2) hab
  exact (ofYoungWeightedLex w).injective
    ((toLex (α := σ →₀ ℕ)).injective h)

noncomputable instance : LinearOrder (YoungWeightedLex w) :=
  LinearOrder.lift' (key_metriccodes2_a7f44027 w) (key_injective_metriccodes2_a7f44027 w)

theorem lt_iff {a b : YoungWeightedLex w} :
    a < b ↔
      (Finsupp.weight w) (ofYoungWeightedLex w a) <
          (Finsupp.weight w) (ofYoungWeightedLex w b) ∨
        (Finsupp.weight w) (ofYoungWeightedLex w a) =
            (Finsupp.weight w) (ofYoungWeightedLex w b) ∧
          toLex (ofYoungWeightedLex w a) <
            toLex (ofYoungWeightedLex w b) := by
  change key_metriccodes2_a7f44027 w a < key_metriccodes2_a7f44027 w b ↔ _
  exact Prod.Lex.toLex_lt_toLex

theorem le_iff {a b : YoungWeightedLex w} :
    a ≤ b ↔
      (Finsupp.weight w) (ofYoungWeightedLex w a) <
          (Finsupp.weight w) (ofYoungWeightedLex w b) ∨
        (Finsupp.weight w) (ofYoungWeightedLex w a) =
            (Finsupp.weight w) (ofYoungWeightedLex w b) ∧
          toLex (ofYoungWeightedLex w a) ≤
            toLex (ofYoungWeightedLex w b) := by
  change key_metriccodes2_a7f44027 w a ≤ key_metriccodes2_a7f44027 w b ↔ _
  exact Prod.Lex.toLex_le_toLex

instance : IsOrderedCancelAddMonoid (YoungWeightedLex w) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofYoungWeightedLex_add, map_add, add_lt_add_iff_left,
      add_right_inj, toLex_add, add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa only [ofYoungWeightedLex_add, map_add, add_lt_add_iff_right, Nat.add_right_cancel_iff,
      toLex_add, add_le_add_iff_right] using h

variable [WellFoundedGT σ]

instance : WellFoundedLT (YoungWeightedLex w) where
  wf := by
    have hlex : WellFounded (Finsupp.Lex (α := σ) (· < ·) (· < ·)) :=
      Finsupp.Lex.wellFounded' (fun _ => Nat.not_lt_zero _)
        (inferInstance : WellFoundedLT ℕ).wf wellFounded_gt
    have hprod := WellFounded.prod_lex
      (inferInstance : WellFoundedLT ℕ).wf hlex
    exact hprod.onFun

end LinearOrder

end YoungWeightedLex

/-- The weighted monomial order used in the spherical-code argument. -/
def weightedMonomialOrder {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]
    (w : σ → ℕ) : MonomialOrder σ where
  syn := YoungWeightedLex w
  toSyn :=
    { toEquiv := toYoungWeightedLex w
      map_add' := YoungWeightedLex.toYoungWeightedLex_add w }
  toSyn_monotone := by
    intro a b hab
    rw [YoungWeightedLex.le_iff]
    by_cases hweight : (Finsupp.weight w) a < (Finsupp.weight w) b
    · exact Or.inl hweight
    · right
      constructor
      · apply le_antisymm _ (Nat.le_of_not_gt hweight)
        rw [← add_tsub_cancel_of_le hab, map_add]
        exact Nat.le_add_right _ _
      · exact Finsupp.toLex_monotone hab

theorem weightedMonomialOrder_lt_iff
    {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]
    (w : σ → ℕ) (a b : σ →₀ ℕ) :
    a ≺[weightedMonomialOrder w] b ↔
      (Finsupp.weight w) a < (Finsupp.weight w) b ∨
        (Finsupp.weight w) a = (Finsupp.weight w) b ∧ toLex a < toLex b :=
  YoungWeightedLex.lt_iff w

theorem weightedMonomialOrder_lt_of_weight_lt
    {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]
    {w : σ → ℕ} {a b : σ →₀ ℕ}
    (h : (Finsupp.weight w) a < (Finsupp.weight w) b) :
    a ≺[weightedMonomialOrder w] b :=
  (weightedMonomialOrder_lt_iff w a b).2 (Or.inl h)

namespace ArbitraryRankMixedTraceRegularity

theorem gramVariableWeight_nonneg {r n : ℕ}
    (i : Fin (r + 1)) (k : Fin n) :
    0 ≤ gramVariableWeight r n i k := by
  have hi : i.val ≤ r := by omega
  have hk : k.val < n := k.isLt
  have hlow : -((n + 2 * r : ℕ) : ℤ) ≤
      (k.val : ℤ) - 2 * (i.val : ℤ) := by
    push_cast
    omega
  have hupp : (k.val : ℤ) - 2 * (i.val : ℤ) ≤
      ((n + 2 * r : ℕ) : ℤ) := by
    push_cast
    omega
  unfold gramVariableWeight
  nlinarith [mul_nonneg (sub_nonneg.mpr hupp)
    (show 0 ≤ ((n + 2 * r : ℕ) : ℤ) +
      ((k.val : ℤ) - 2 * (i.val : ℤ)) by linarith)]

/-- The gram variable nat weight used in the spherical-code argument. -/
def gramVariableNatWeight (r n : ℕ)
    (a : Fin ((r + 1) * n)) : ℕ :=
  let z := (finProdFinEquiv (m := r + 1) (n := n)).symm a
  (gramVariableWeight r n z.1 z.2).toNat

@[simp] theorem gramVariableNatWeight_variableIndex {r n : ℕ}
    (i : Fin (r + 1)) (k : Fin n) :
    gramVariableNatWeight r n (variableIndex i k) =
      (gramVariableWeight r n i k).toNat := by
  simp only [gramVariableNatWeight, variableIndex, Equiv.symm_apply_apply]

theorem gramSummandExponent_natWeight {r n : ℕ}
    (z : UpperGramPair r) (k : Fin n) :
    (Finsupp.weight (gramVariableNatWeight r n))
        (gramSummandExponent z k) =
      (gramSummandWeight z k).toNat := by
  rw [gramSummandExponent, map_add, Finsupp.weight_single,
    Finsupp.weight_single]
  simp only [one_smul, gramVariableNatWeight_variableIndex]
  exact (Int.toNat_add (gramVariableWeight_nonneg z.val.1 k)
    (gramVariableWeight_nonneg z.val.2 k)).symm

theorem gramPivot_unique_max_natWeight {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r)
    (k : Fin n) (hk : k ≠ gramPivot hn z) :
    (Finsupp.weight (gramVariableNatWeight r n))
        (gramSummandExponent z k) <
      (Finsupp.weight (gramVariableNatWeight r n))
        (gramPivotExponent hn z) := by
  change (Finsupp.weight (gramVariableNatWeight r n))
      (gramSummandExponent z k) <
    (Finsupp.weight (gramVariableNatWeight r n))
      (gramSummandExponent z (gramPivot hn z))
  rw [gramSummandExponent_natWeight, gramSummandExponent_natWeight]
  have h := gramPivot_unique_max_weight hn z k hk
  have hk_nonneg : 0 ≤ gramSummandWeight z k :=
    add_nonneg (gramVariableWeight_nonneg z.val.1 k)
      (gramVariableWeight_nonneg z.val.2 k)
  have hp_nonneg : 0 ≤ gramSummandWeight z (gramPivot hn z) :=
    add_nonneg (gramVariableWeight_nonneg z.val.1 (gramPivot hn z))
      (gramVariableWeight_nonneg z.val.2 (gramPivot hn z))
  exact_mod_cast (show
    ((gramSummandWeight z k).toNat : ℤ) <
      ((gramSummandWeight z (gramPivot hn z)).toNat : ℤ) by
        simpa only [Int.toNat_of_nonneg hk_nonneg, Int.toNat_of_nonneg hp_nonneg] using h)

theorem gramPairPolynomial_support_exponent {r n : ℕ}
    (z : UpperGramPair r)
    {d : Fin ((r + 1) * n) →₀ ℕ}
    (hd : d ∈ (gramPairPolynomial n z).support) :
    ∃ k : Fin n, d = gramSummandExponent z k := by
  classical
  unfold gramPairPolynomial rowPairingPolynomial at hd
  have hsum := MvPolynomial.support_sum hd
  obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hsum
  refine ⟨k, ?_⟩
  symm
  simpa only [gramSummandExponent, MvPolynomial.X, MvPolynomial.monomial_mul, mul_one,
    MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, ne_eq, ite_eq_right_iff, one_ne_zero,
    imp_false, Decidable.not_not] using hk

theorem gramPairPolynomial_weighted_degree {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r) :
    (weightedMonomialOrder (gramVariableNatWeight r n)).degree
      (gramPairPolynomial n z) = gramPivotExponent hn z := by
  let m := weightedMonomialOrder (gramVariableNatWeight r n)
  apply m.toSyn.injective
  apply le_antisymm
  · apply MonomialOrder.degree_le_iff.mpr
    intro d hd
    obtain ⟨k, rfl⟩ := gramPairPolynomial_support_exponent z hd
    by_cases hk : k = gramPivot hn z
    · subst k
      exact le_rfl
    · exact le_of_lt (weightedMonomialOrder_lt_of_weight_lt
        (gramPivot_unique_max_natWeight hn z k hk))
  · apply MonomialOrder.le_degree
    rw [MvPolynomial.mem_support_iff,
      coeff_gramPairPolynomial_pivot hn z]
    exact one_ne_zero

theorem gramPairPolynomial_weighted_leadingCoeff {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r) :
    (weightedMonomialOrder (gramVariableNatWeight r n)).leadingCoeff
      (gramPairPolynomial n z) = 1 := by
  rw [MonomialOrder.leadingCoeff,
    gramPairPolynomial_weighted_degree hn z]
  exact coeff_gramPairPolynomial_pivot hn z

theorem gramPairPolynomial_weighted_monic {r n : ℕ}
    (hn : 2 * r < n) (z : UpperGramPair r) :
    (weightedMonomialOrder (gramVariableNatWeight r n)).Monic
      (gramPairPolynomial n z) :=
  gramPairPolynomial_weighted_leadingCoeff hn z

theorem gramPairPolynomial_weighted_degree_support_disjoint
    {r n : ℕ} (hn : 2 * r < n)
    (z w : UpperGramPair r) (hzw : z ≠ w) :
    Disjoint
      ((weightedMonomialOrder (gramVariableNatWeight r n)).degree
        (gramPairPolynomial n z)).support
      ((weightedMonomialOrder (gramVariableNatWeight r n)).degree
        (gramPairPolynomial n w)).support := by
  rw [gramPairPolynomial_weighted_degree hn z,
    gramPairPolynomial_weighted_degree hn w]
  exact gramPivotExponent_support_disjoint hn z w hzw

end ArbitraryRankMixedTraceRegularity

end

section


open scoped BigOperators MonomialOrder

theorem finsupp_sup_eq_add_of_disjoint_support
    {σ : Type*} (a b : σ →₀ ℕ)
    (h : Disjoint a.support b.support) :
    a ⊔ b = a + b := by
  ext i
  by_cases ha : a i = 0
  · simp only [Finsupp.sup_apply, ha, zero_le, sup_of_le_right, Finsupp.coe_add, Pi.add_apply,
      zero_add]
  · have hb : b i = 0 := by
      by_contra hb
      exact (Finset.disjoint_left.mp h)
        (Finsupp.mem_support_iff.mpr ha)
        (Finsupp.mem_support_iff.mpr hb)
    simp only [Finsupp.sup_apply, hb, zero_le, sup_of_le_left, Finsupp.coe_add, Pi.add_apply,
      add_zero]

theorem coprime_sPolynomial_eq
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (f g : MvPolynomial σ K)
    (hf : m.Monic f) (hg : m.Monic g)
    (h : Disjoint (m.degree f).support (m.degree g).support) :
    m.sPolynomial f g =
      (m.leadingTerm g - g) * f +
        (f - m.leadingTerm f) * g := by
  rw [m.sPolynomial_def,
    finsupp_sup_eq_add_of_disjoint_support _ _ h,
    hf.leadingCoeff_eq_one, hg.leadingCoeff_eq_one]
  have hsub₁ : m.degree f + m.degree g - m.degree f = m.degree g := by
    ext i
    simp only [add_tsub_cancel_left]
  have hsub₂ : m.degree f + m.degree g - m.degree g = m.degree f := by
    ext i
    simp only [add_tsub_cancel_right]
  rw [hsub₁, hsub₂]
  simp only [MonomialOrder.leadingTerm,
    hf.leadingCoeff_eq_one, hg.leadingCoeff_eq_one]
  ring

theorem coprime_sPolynomial_left_product_lt
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (f g : MvPolynomial σ K)
    (hf : m.Monic f)
    (hterm : (m.leadingTerm g - g) * f ≠ 0) :
    m.degree ((m.leadingTerm g - g) * f) ≺[m]
      m.degree f + m.degree g := by
  have htail : g - m.leadingTerm g ≠ 0 := by
    intro hzero
    apply hterm
    rw [← neg_sub, hzero, neg_zero, zero_mul]
  have htail' : m.leadingTerm g - g ≠ 0 := by
    intro hzero
    apply htail
    rw [← neg_sub, hzero, neg_zero]
  have hdegree : m.degree g ≠ 0 :=
    m.degree_ne_zero_of_sub_leadingTerm_ne_zero htail
  have hlt := m.degree_sub_leadingTerm_lt_degree hdegree
  rw [m.degree_mul htail' hf.ne_zero,
    show m.leadingTerm g - g = -(g - m.leadingTerm g) by ring,
    m.degree_neg, map_add, map_add]
  simpa only [add_comm, add_lt_add_iff_left,
    gt_iff_lt] using add_lt_add_right hlt (m.toSyn (m.degree f))

theorem coprime_sPolynomial_right_product_lt
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (f g : MvPolynomial σ K)
    (hg : m.Monic g)
    (hterm : (f - m.leadingTerm f) * g ≠ 0) :
    m.degree ((f - m.leadingTerm f) * g) ≺[m]
      m.degree f + m.degree g := by
  have htail : f - m.leadingTerm f ≠ 0 := by
    intro hzero
    exact hterm (by rw [hzero, zero_mul])
  have hdegree : m.degree f ≠ 0 :=
    m.degree_ne_zero_of_sub_leadingTerm_ne_zero htail
  have hlt := m.degree_sub_leadingTerm_lt_degree hdegree
  rw [m.degree_mul htail hg.ne_zero, map_add, map_add]
  simpa only [add_comm, gt_iff_lt] using add_lt_add_right hlt (m.toSyn (m.degree g))

theorem coprime_sPolynomial_monomial_left_product_lt
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (f g : MvPolynomial σ K)
    (hf : m.Monic f)
    (c : σ →₀ ℕ) (a : K)
    (hterm :
      MvPolynomial.monomial c a *
        ((m.leadingTerm g - g) * f) ≠ 0) :
    m.degree
        (MvPolynomial.monomial c a *
          ((m.leadingTerm g - g) * f)) ≺[m]
      c + m.degree f + m.degree g := by
  classical
  have hmono : MvPolynomial.monomial c a ≠ 0 := by
    intro hz
    exact hterm (by rw [hz, zero_mul])
  have hproduct : (m.leadingTerm g - g) * f ≠ 0 := by
    intro hz
    exact hterm (by rw [hz, mul_zero])
  have ha : a ≠ 0 := by
    intro hz
    exact hmono (by simp only [hz, MvPolynomial.monomial_zero])
  have hlt := coprime_sPolynomial_left_product_lt m f g hf hproduct
  rw [m.degree_mul hmono hproduct, m.degree_monomial, ite_eq_right ha,
    map_add, map_add, map_add]
  simpa only [add_comm, add_left_comm, add_lt_add_iff_left, gt_iff_lt, map_add] using
    add_lt_add_left hlt (m.toSyn c)

theorem coprime_sPolynomial_monomial_right_product_lt
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (f g : MvPolynomial σ K)
    (hg : m.Monic g)
    (c : σ →₀ ℕ) (a : K)
    (hterm :
      MvPolynomial.monomial c a *
        ((f - m.leadingTerm f) * g) ≠ 0) :
    m.degree
        (MvPolynomial.monomial c a *
          ((f - m.leadingTerm f) * g)) ≺[m]
      c + m.degree f + m.degree g := by
  classical
  have hmono : MvPolynomial.monomial c a ≠ 0 := by
    intro hz
    exact hterm (by rw [hz, zero_mul])
  have hproduct : (f - m.leadingTerm f) * g ≠ 0 := by
    intro hz
    exact hterm (by rw [hz, mul_zero])
  have ha : a ≠ 0 := by
    intro hz
    exact hmono (by simp only [hz, MvPolynomial.monomial_zero])
  have hlt := coprime_sPolynomial_right_product_lt m f g hg hproduct
  rw [m.degree_mul hmono hproduct, m.degree_monomial, ite_eq_right ha,
    map_add, map_add, map_add]
  simpa only [add_comm, add_left_comm, add_lt_add_iff_left, gt_iff_lt, map_add] using
    add_lt_add_left hlt (m.toSyn c)

end

end HigherHarmonicYoung

section


open scoped BigOperators MonomialOrder

namespace HigherYoungCoprimeLeadingBuchberger

open MvPolynomial
open MetricCodes.Spherical.HigherHarmonicYoung

theorem mem_ofList_iff_exists_linearCombination
    {σ K : Type*} [Field K]
    (fs : List (MvPolynomial σ K)) (p : MvPolynomial σ K) :
    p ∈ Ideal.ofList fs ↔
      ∃ g : {f : MvPolynomial σ K // f ∈ fs} →₀ MvPolynomial σ K,
        Finsupp.linearCombination (MvPolynomial σ K)
          (fun f : {f : MvPolynomial σ K // f ∈ fs} =>
            (f : MvPolynomial σ K)) g = p := by
  change p ∈ Ideal.span {f : MvPolynomial σ K | f ∈ fs} ↔ _
  have hrange :
      Set.range
          (fun f : {f : MvPolynomial σ K // f ∈ fs} =>
            (f : MvPolynomial σ K)) =
        {f : MvPolynomial σ K | f ∈ fs} := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact g.property
    · intro hf
      exact ⟨⟨f, hf⟩, rfl⟩
  rw [← hrange, Finsupp.mem_ideal_span_range_iff_exists_finsupp]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul] using hg
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    simpa only [Finsupp.sum, Finsupp.linearCombination_apply, smul_eq_mul] using hg

private def representationDegree {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K) : m.syn :=
  g.support.sup fun i => m.toSyn (m.degree (b i * g i))

theorem degree_mul_le_representationDegree
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K)
    (i : ι) (hi : g i ≠ 0) :
    m.toSyn (m.degree (b i * g i)) ≤ representationDegree m b g := by
  exact Finset.le_sup (f := fun j => m.toSyn (m.degree (b j * g j)))
    (Finsupp.mem_support_iff.mpr hi)

theorem degree_mul_le_representationDegree_all
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K)
    (i : ι) :
    m.toSyn (m.degree (b i * g i)) ≤ representationDegree m b g := by
  classical
  by_cases hi : g i = 0
  · simp only [hi, mul_zero, MonomialOrder.degree_zero, map_zero, MonomialOrder.zero_le]
  · exact degree_mul_le_representationDegree m b g i hi

theorem exists_minimalRepresentation
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (p : MvPolynomial σ K)
    (hrep : ∃ g : ι →₀ MvPolynomial σ K,
      Finsupp.linearCombination (MvPolynomial σ K) b g = p) :
    ∃ g : ι →₀ MvPolynomial σ K,
      Finsupp.linearCombination (MvPolynomial σ K) b g = p ∧
      ∀ h : ι →₀ MvPolynomial σ K,
        Finsupp.linearCombination (MvPolynomial σ K) b h = p →
          representationDegree m b g ≤ representationDegree m b h := by
  obtain ⟨g, hg⟩ := exists_minimalFor_of_wellFoundedLT
    (fun g : ι →₀ MvPolynomial σ K =>
      Finsupp.linearCombination (MvPolynomial σ K) b g = p)
    (representationDegree m b) hrep
  exact ⟨g, hg.prop, fun h hh => hg.le hh⟩

theorem degree_linearCombination_le_representationDegree
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K) :
    m.toSyn
      (m.degree (Finsupp.linearCombination (MvPolynomial σ K) b g)) ≤
        representationDegree m b g := by
  classical
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_comm,
    representationDegree] using
    (m.degree_sum_le (s := g.support) (f := fun i => b i * g i))

theorem representationDegree_add_le
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g h : ι →₀ MvPolynomial σ K) :
    representationDegree m b (g + h) ≤
      representationDegree m b g ⊔ representationDegree m b h := by
  classical
  unfold representationDegree
  apply Finset.sup_le
  intro i _
  rw [Finsupp.add_apply, mul_add]
  exact le_trans m.degree_add_le
    (sup_le_sup (degree_mul_le_representationDegree_all m b g i)
      (degree_mul_le_representationDegree_all m b h i))

theorem representationDegree_lt_of_forall
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K)
    (d : m.syn) (hd : (⊥ : m.syn) < d)
    (hterm : ∀ i : ι, g i ≠ 0 →
      m.toSyn (m.degree (b i * g i)) < d) :
    representationDegree m b g < d := by
  classical
  apply (Finset.sup_lt_iff hd).mpr
  intro i hi
  exact hterm i (Finsupp.mem_support_iff.mp hi)

theorem representationDegree_sum_lt
    {σ K ι α : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (s : Finset α)
    (g : α → ι →₀ MvPolynomial σ K)
    (d : m.syn) (hd : (⊥ : m.syn) < d)
    (hterm : ∀ a ∈ s, representationDegree m b (g a) < d) :
    representationDegree m b (∑ a ∈ s, g a) < d := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [representationDegree, Finset.sum_empty, Finsupp.support_zero,
               Finsupp.coe_zero, Pi.zero_apply, mul_zero, MonomialOrder.degree_zero, map_zero,
               Finset.sup_empty, MonomialOrder.bot_eq_zero] using hd
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact lt_of_le_of_lt
        (representationDegree_add_le m b (g a) (∑ j ∈ s, g j))
        ((max_lt_iff).mpr
          ⟨hterm a (Finset.mem_insert_self _ _),
            ih (fun j hj => hterm j (Finset.mem_insert_of_mem hj))⟩)

theorem representationDegree_sum_sum_lt
    {σ K ι α β : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (s : Finset α) (t : Finset β)
    (g : α → β → ι →₀ MvPolynomial σ K)
    (d : m.syn) (hd : (⊥ : m.syn) < d)
    (hterm : ∀ a ∈ s, ∀ a' ∈ t,
      representationDegree m b (g a a') < d) :
    representationDegree m b (∑ a ∈ s, ∑ a' ∈ t, g a a') < d := by
  apply representationDegree_sum_lt m b s _ d hd
  intro a ha
  exact representationDegree_sum_lt m b t _ d hd (hterm a ha)

theorem representationDegree_add_sum_sum_lt
    {σ K ι α β : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (r : ι →₀ MvPolynomial σ K)
    (s : Finset α) (t : Finset β)
    (g : α → β → ι →₀ MvPolynomial σ K)
    (d : m.syn) (hd : (⊥ : m.syn) < d)
    (hr : representationDegree m b r < d)
    (hterm : ∀ a ∈ s, ∀ a' ∈ t,
      representationDegree m b (g a a') < d) :
    representationDegree m b
      (r + ∑ a ∈ s, ∑ a' ∈ t, g a a') < d := by
  apply lt_of_le_of_lt
    (representationDegree_add_le m b r (∑ a ∈ s, ∑ a' ∈ t, g a a'))
  exact (max_lt_iff).mpr
    ⟨hr, representationDegree_sum_sum_lt m b s t g d hd hterm⟩

theorem representationDegree_single_lt
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (i : ι) (x : MvPolynomial σ K)
    (d : m.syn) (hd : (⊥ : m.syn) < d)
    (hx : b i * x = 0 ∨ m.toSyn (m.degree (b i * x)) < d) :
    representationDegree m b (Finsupp.single i x) < d := by
  classical
  apply representationDegree_lt_of_forall m b _ d hd
  intro j hj
  have hji : j = i := by
    by_contra hne
    exact hj (Finsupp.single_eq_of_ne hne)
  subst j
  rcases hx with hzero | hlt
  · simpa only [Finsupp.single_eq_same, hzero, MonomialOrder.degree_zero, map_zero, gt_iff_lt,
      MonomialOrder.bot_eq_zero] using hd
  · simpa only [Finsupp.single_eq_same, gt_iff_lt] using hlt

theorem representationDegree_pair_lt
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (i j : ι) (x y : MvPolynomial σ K)
    (d : m.syn) (hd : (⊥ : m.syn) < d)
    (hx : b i * x = 0 ∨ m.toSyn (m.degree (b i * x)) < d)
    (hy : b j * y = 0 ∨ m.toSyn (m.degree (b j * y)) < d) :
    representationDegree m b
      (Finsupp.single i x + Finsupp.single j y) < d := by
  exact lt_of_le_of_lt (representationDegree_add_le m b _ _)
    ((max_lt_iff).mpr
      ⟨representationDegree_single_lt m b i x d hd hx,
       representationDegree_single_lt m b j y d hd hy⟩)

theorem exists_topRepresentationIndex
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K)
    (hg : g ≠ 0) :
    ∃ i : ι, g i ≠ 0 ∧
      m.toSyn (m.degree (b i * g i)) = representationDegree m b g := by
  classical
  have hsupport : g.support.Nonempty := Finsupp.support_nonempty_iff.mpr hg
  obtain ⟨i, hi, hmax⟩ :=
    Finset.sup_mem_of_nonempty
      (f := fun j => m.toSyn (m.degree (b j * g j))) hsupport
  exact ⟨i, Finsupp.mem_support_iff.mp hi, hmax⟩

theorem exists_topRepresentationIndex_of_ne_zero
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (p : MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K)
    (hrep : Finsupp.linearCombination (MvPolynomial σ K) b g = p)
    (hp : p ≠ 0) :
    ∃ i : ι, g i ≠ 0 ∧
      m.toSyn (m.degree (b i * g i)) = representationDegree m b g := by
  apply exists_topRepresentationIndex m b g
  intro hg
  subst g
  exact hp (by simpa only [map_zero] using hrep.symm)

theorem exists_degree_le_of_representationImprovement
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (hb : ∀ i : ι, b i ≠ 0)
    (p : MvPolynomial σ K)
    (hp : p ≠ 0)
    (hrep : ∃ g : ι →₀ MvPolynomial σ K,
      Finsupp.linearCombination (MvPolynomial σ K) b g = p)
    (himprove : ∀ g : ι →₀ MvPolynomial σ K,
      Finsupp.linearCombination (MvPolynomial σ K) b g = p →
      m.toSyn (m.degree p) < representationDegree m b g →
        ∃ h : ι →₀ MvPolynomial σ K,
          Finsupp.linearCombination (MvPolynomial σ K) b h = p ∧
          representationDegree m b h < representationDegree m b g) :
    ∃ i : ι, m.degree (b i) ≤ m.degree p := by
  obtain ⟨g, hg, hminimal⟩ := exists_minimalRepresentation m b p hrep
  have hbound : m.toSyn (m.degree p) ≤ representationDegree m b g := by
    simpa only [hg] using degree_linearCombination_le_representationDegree m b g
  have hnot : ¬ m.toSyn (m.degree p) < representationDegree m b g := by
    intro hlt
    obtain ⟨h, hh, hstrict⟩ := himprove g hg hlt
    exact (not_lt_of_ge (hminimal h hh)) hstrict
  have hdegree : m.toSyn (m.degree p) = representationDegree m b g :=
    le_antisymm hbound (le_of_not_gt hnot)
  obtain ⟨i, hi, htop⟩ :=
    exists_topRepresentationIndex_of_ne_zero m b p g hg hp
  refine ⟨i, ?_⟩
  have heq : m.degree (b i * g i) = m.degree p :=
    m.toSyn.injective (htop.trans hdegree.symm)
  rw [m.degree_mul (hb i) hi] at heq
  rw [← heq]
  exact self_le_add_right _ _

theorem top_leading_multiple_sPolynomial_decomposition
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (B : Finset ι)
    (b q : ι → MvPolynomial σ K)
    (d : m.syn)
    (hd : ∀ i ∈ B,
      m.toSyn (m.degree (m.leadingTerm (q i) * b i)) = d ∨
        m.leadingTerm (q i) * b i = 0)
    (hsum : m.toSyn
      (m.degree (∑ i ∈ B, m.leadingTerm (q i) * b i)) < d) :
    ∃ c : ι → ι → K,
      (∑ i ∈ B, m.leadingTerm (q i) * b i) =
        ∑ i ∈ B, ∑ j ∈ B, c i j •
          (MvPolynomial.monomial
            (m.degree (q i * b i) ⊔ m.degree (q j * b j) -
              m.degree (b i) ⊔ m.degree (b j))
            (m.leadingCoeff (q i) * m.leadingCoeff (q j)) *
            m.sPolynomial (b i) (b j)) := by
  obtain ⟨c, hc⟩ := m.sPolynomial_decomposition'
    (fun i => m.leadingTerm (q i) * b i) hd hsum
  refine ⟨c, ?_⟩
  simpa only [m.sPolynomial_leadingTerm_mul'] using hc

theorem top_leadingTerm_sum_degree_lt
    {σ K ι : Type*} [Field K] [DecidableEq σ]
    (m : MonomialOrder σ)
    (b g : ι → MvPolynomial σ K)
    (s : Finset ι) (D : σ →₀ ℕ)
    (hbound : ∀ i ∈ s,
      m.toSyn (m.degree (b i * g i)) ≤ m.toSyn D)
    (htotal : m.toSyn
      (m.degree (∑ i ∈ s, b i * g i)) < m.toSyn D) :
    m.toSyn (m.degree
      (∑ i ∈ s.filter
        (fun i => m.degree (b i * g i) = D),
        m.leadingTerm (g i) * b i)) < m.toSyn D := by
  classical
  let T : Finset ι := s.filter
    (fun i => m.degree (b i * g i) = D)
  let q : MvPolynomial σ K :=
    ∑ i ∈ T, m.leadingTerm (g i) * b i
  have hdegree : m.toSyn (m.degree q) ≤ m.toSyn D := by
    calc
      m.toSyn (m.degree q) ≤
          T.sup (fun i =>
            m.toSyn (m.degree (m.leadingTerm (g i) * b i))) :=
        m.degree_sum_le
      _ ≤ m.toSyn D := by
        apply Finset.sup_le
        intro i hi
        have hitop := (Finset.mem_filter.mp hi).2
        rw [m.degree_leadingTerm_mul, mul_comm, hitop]
  have hcoeff : q.coeff D =
      (∑ i ∈ s, b i * g i).coeff D := by
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
    dsimp [q, T]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hitop : m.degree (b i * g i) = D
    · simp only [hitop, ↓reduceIte]
      have hlead :
          m.degree (m.leadingTerm (g i) * b i) = D := by
        rw [m.degree_leadingTerm_mul, mul_comm, hitop]
      calc
        (m.leadingTerm (g i) * b i).coeff D =
            m.leadingCoeff (m.leadingTerm (g i) * b i) := by
              rw [MonomialOrder.leadingCoeff, hlead]
        _ = m.leadingCoeff (b i * g i) := by
              simp only [mul_comm, m.leadingCoeff_mul, MonomialOrder.leadingCoeff_leadingTerm]
        _ = (b i * g i).coeff D := by
              rw [MonomialOrder.leadingCoeff, hitop]
    · simp only [hitop, ↓reduceIte]
      have hlt : m.toSyn (m.degree (b i * g i)) < m.toSyn D :=
        lt_of_le_of_ne (hbound i hi) (by
          intro h
          exact hitop (m.toSyn.injective h))
      exact (m.coeff_eq_zero_of_lt hlt).symm
  have hcoeffzero : q.coeff D = 0 := by
    rw [hcoeff]
    exact m.coeff_eq_zero_of_lt htotal
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at htotal
    exact (not_lt_bot htotal)
  apply lt_of_le_of_ne hdegree
  intro heq
  have hdeg : m.degree q = D := m.toSyn.injective heq
  have hq : q ≠ 0 := by
    intro hzero
    apply hD
    simpa only [hzero, MonomialOrder.degree_zero] using hdeg.symm
  exact (m.coeff_degree_ne_zero_iff.mpr hq)
    (by simpa only [hdeg] using hcoeffzero)

theorem linearCombination_top_reassembly
    {R ι : Type*} [CommRing R]
    (b : ι → R) (g : ι →₀ R) (B : Finset ι)
    (u : ι → R) (v w : ι → ι → R)
    (hreplace :
      (∑ i ∈ B, u i * b i) =
        ∑ i ∈ B, ∑ j ∈ B, (v i j * b i + w i j * b j)) :
    Finsupp.linearCombination R b
        (g - ∑ i ∈ B, Finsupp.single i (u i) +
          ∑ i ∈ B, ∑ j ∈ B,
            (Finsupp.single i (v i j) + Finsupp.single j (w i j))) =
      Finsupp.linearCombination R b g := by
  classical
  have hremove :
      Finsupp.linearCombination R b
          (∑ i ∈ B, Finsupp.single i (u i)) =
        ∑ i ∈ B, u i * b i := by
    simp only [map_sum, Finsupp.linearCombination_single, smul_eq_mul]
  have hrestore :
      Finsupp.linearCombination R b
          (∑ i ∈ B, ∑ j ∈ B,
            (Finsupp.single i (v i j) + Finsupp.single j (w i j))) =
        ∑ i ∈ B, ∑ j ∈ B, (v i j * b i + w i j * b j) := by
    simp only [map_sum, map_add, Finsupp.linearCombination_single, smul_eq_mul]
  rw [map_add, map_sub, hremove, hrestore, hreplace]
  ring

theorem linearCombination_buchberger_reassembly
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K)
    (B : Finset ι)
    (c : ι → ι → K)
    (P : ι → ι → MvPolynomial σ K)
    (hreplace :
      (∑ i ∈ B, m.leadingTerm (g i) * b i) =
        ∑ i ∈ B, ∑ j ∈ B, c i j •
          (P i j * ((m.leadingTerm (b j) - b j) * b i +
            (b i - m.leadingTerm (b i)) * b j))) :
    Finsupp.linearCombination (MvPolynomial σ K) b
        (g - ∑ i ∈ B, Finsupp.single i (m.leadingTerm (g i)) +
          ∑ i ∈ B, ∑ j ∈ B,
            (Finsupp.single i
              (c i j • (P i j * (m.leadingTerm (b j) - b j))) +
             Finsupp.single j
              (c i j • (P i j * (b i - m.leadingTerm (b i)))))) =
      Finsupp.linearCombination (MvPolynomial σ K) b g := by
  apply linearCombination_top_reassembly b g B
    (fun i => m.leadingTerm (g i))
    (fun i j => c i j • (P i j * (m.leadingTerm (b j) - b j)))
    (fun i j => c i j • (P i j * (b i - m.leadingTerm (b i))))
  calc
    (∑ i ∈ B, m.leadingTerm (g i) * b i) =
        ∑ i ∈ B, ∑ j ∈ B, c i j •
          (P i j * ((m.leadingTerm (b j) - b j) * b i +
            (b i - m.leadingTerm (b i)) * b j)) := hreplace
    _ = ∑ i ∈ B, ∑ j ∈ B,
          ((c i j • (P i j * (m.leadingTerm (b j) - b j))) * b i +
            (c i j • (P i j * (b i - m.leadingTerm (b i)))) * b j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Algebra.smul_def, algebraMap_eq]
      ring

theorem representationDegree_strip_top_leading_terms_lt
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (g : ι →₀ MvPolynomial σ K)
    (B : Finset ι)
    (d : m.syn)
    (hd : (⊥ : m.syn) < d)
    (hb : ∀ i : ι, b i ≠ 0)
    (hbound : ∀ i : ι,
      m.toSyn (m.degree (b i * g i)) ≤ d)
    (hB : ∀ i : ι,
      i ∈ B ↔ g i ≠ 0 ∧ m.toSyn (m.degree (b i * g i)) = d) :
    representationDegree m b
      (g - ∑ i ∈ B, Finsupp.single i (m.leadingTerm (g i))) < d := by
  classical
  apply (Finset.sup_lt_iff hd).mpr
  intro i hi
  have hcoefficient :
      (g - ∑ j ∈ B, Finsupp.single j (m.leadingTerm (g j))) i ≠ 0 :=
    Finsupp.mem_support_iff.mp hi
  have hslice :
      (∑ j ∈ B, Finsupp.single j (m.leadingTerm (g j))) i =
        if i ∈ B then m.leadingTerm (g i) else 0 := by
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  rw [Finsupp.sub_apply, hslice] at hcoefficient ⊢
  by_cases hiB : i ∈ B
  · simp only [ite_eq_left hiB] at hcoefficient ⊢
    obtain ⟨hgi, htop⟩ := (hB i).mp hiB
    have hdegree := m.degree_ne_zero_of_sub_leadingTerm_ne_zero hcoefficient
    have hsmall := m.degree_sub_leadingTerm_lt_degree hdegree
    rw [m.degree_mul (hb i) hcoefficient, map_add]
    calc
      m.toSyn (m.degree (b i)) +
          m.toSyn (m.degree (g i - m.leadingTerm (g i))) <
        m.toSyn (m.degree (b i)) + m.toSyn (m.degree (g i)) :=
          by simpa only [add_lt_add_iff_left] using add_lt_add_right hsmall (m.toSyn (m.degree
            (b i)))
      _ = d := by
        rw [← map_add, ← m.degree_mul (hb i) hgi]
        exact htop
  · simp only [ite_eq_right hiB, sub_zero] at hcoefficient ⊢
    exact lt_of_le_of_ne (hbound i)
      (fun heq => hiB ((hB i).mpr ⟨hcoefficient, heq⟩))

private theorem buchberger_correction_pair_lt
    {σ K ι : Type*} [Field K] [DecidableEq ι]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (hmonic : ∀ i : ι, m.Monic (b i))
    (hdisjoint : ∀ i j : ι, i ≠ j →
      Disjoint (m.degree (b i)).support (m.degree (b j)).support)
    (g : ι →₀ MvPolynomial σ K)
    (d : m.syn)
    (i j : ι)
    (hi : i ∈ g.support.filter
      (fun k => m.toSyn (m.degree (b k * g k)) = d))
    (hj : j ∈ g.support.filter
      (fun k => m.toSyn (m.degree (b k * g k)) = d))
    (Pij : MvPolynomial σ K)
    (hPij : Pij = if i = j then 0 else
      MvPolynomial.monomial
        (m.degree (g i * b i) ⊔ m.degree (g j * b j) -
          m.degree (b i) ⊔ m.degree (b j))
        (m.leadingCoeff (g i) * m.leadingCoeff (g j)))
    (cij : K) :
    (b i * (cij • (Pij * (m.leadingTerm (b j) - b j))) = 0 ∨
      m.toSyn (m.degree
        (b i * (cij • (Pij * (m.leadingTerm (b j) - b j))))) < d) ∧
    (b j * (cij • (Pij * (b i - m.leadingTerm (b i)))) = 0 ∨
      m.toSyn (m.degree
        (b j * (cij • (Pij * (b i - m.leadingTerm (b i)))))) < d) := by
  constructor
  · by_cases hzero :
        b i * (cij • (Pij * (m.leadingTerm (b j) - b j))) = 0
    · exact Or.inl hzero
    · right
      by_cases hij : i = j
      · subst j
        have hPij0 : Pij = 0 := by simpa only [↓reduceIte] using hPij
        simp only [hPij0, zero_mul, smul_zero, mul_zero, not_true_eq_false] at hzero
      · have hpi := (Finset.mem_filter.mp hi).2
        have hpj := (Finset.mem_filter.mp hj).2
        have hterm : Pij * ((m.leadingTerm (b j) - b j) * b i) ≠ 0 := by
          intro hz
          apply hzero
          rw [Algebra.smul_def]
          calc
            b i * (MvPolynomial.C cij *
                (Pij * (m.leadingTerm (b j) - b j))) =
              MvPolynomial.C cij *
                (Pij * ((m.leadingTerm (b j) - b j) * b i)) := by ring
            _ = 0 := by rw [hz, mul_zero]
        have hlt := coprime_sPolynomial_monomial_left_product_lt
          m (b i) (b j) (hmonic i)
          (m.degree (g i * b i) ⊔ m.degree (g j * b j) -
            m.degree (b i) ⊔ m.degree (b j))
          (m.leadingCoeff (g i) * m.leadingCoeff (g j))
          (by simpa only [ne_eq, mul_eq_zero, monomial_eq_zero,
                MonomialOrder.leadingCoeff_eq_zero_iff, not_or,
                hij, ↓reduceIte, hPij] using hterm)
        have hsuple :
            m.degree (b i) ⊔ m.degree (b j) ≤
              m.degree (g i * b i) ⊔ m.degree (g j * b j) := by
          apply sup_le_sup
          · rw [m.degree_mul
                (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hi).1)
                (hmonic i).ne_zero]
            exact self_le_add_left _ _
          · rw [m.degree_mul
                (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hj).1)
                (hmonic j).ne_zero]
            exact self_le_add_left _ _
        have hsimpl :
            (m.degree (g i * b i) ⊔ m.degree (g j * b j) -
              m.degree (b i) ⊔ m.degree (b j)) +
                m.degree (b i) + m.degree (b j) =
              m.degree (g i * b i) ⊔ m.degree (g j * b j) := by
          have hbase := finsupp_sup_eq_add_of_disjoint_support
            (m.degree (b i)) (m.degree (b j)) (hdisjoint i j hij)
          rw [hbase] at hsuple ⊢
          simpa only [add_assoc] using tsub_add_cancel_of_le hsuple
        have htopij :
            m.toSyn
              (m.degree (g i * b i) ⊔ m.degree (g j * b j)) = d := by
          have hi' : m.degree (g i * b i) = m.toSyn.symm d := by
            apply m.toSyn.injective
            simpa only [AddEquiv.apply_symm_apply, mul_comm] using hpi
          have hj' : m.degree (g j * b j) = m.toSyn.symm d := by
            apply m.toSyn.injective
            simpa only [AddEquiv.apply_symm_apply, mul_comm] using hpj
          simp only [hi', hj', sup_idem, AddEquiv.apply_symm_apply]
        rw [hsimpl] at hlt
        have hscaled :
            m.toSyn (m.degree
              (Pij * ((m.leadingTerm (b j) - b j) * b i))) < d := by
          simpa [hPij, hij, htopij] using hlt
        have hc0 : cij ≠ 0 := by
          intro hz
          simp only [hz, zero_smul, mul_zero, not_true_eq_false] at hzero
        have hrewrite :
            b i * (cij • (Pij * (m.leadingTerm (b j) - b j))) =
              MvPolynomial.C cij *
                (Pij * ((m.leadingTerm (b j) - b j) * b i)) := by
          simp only [Algebra.smul_def, algebraMap_eq]
          ring
        rw [hrewrite, m.degree_mul
          (MvPolynomial.C_ne_zero.mpr hc0) hterm,
          m.degree_C, zero_add]
        exact hscaled
  · by_cases hzero :
        b j * (cij • (Pij * (b i - m.leadingTerm (b i)))) = 0
    · exact Or.inl hzero
    · right
      by_cases hij : i = j
      · subst j
        have hPij0 : Pij = 0 := by simpa only [↓reduceIte] using hPij
        simp only [hPij0, zero_mul, smul_zero, mul_zero, not_true_eq_false] at hzero
      · have hpi := (Finset.mem_filter.mp hi).2
        have hpj := (Finset.mem_filter.mp hj).2
        have hterm : Pij * ((b i - m.leadingTerm (b i)) * b j) ≠ 0 := by
          intro hz
          apply hzero
          rw [Algebra.smul_def]
          calc
            b j * (MvPolynomial.C cij *
                (Pij * (b i - m.leadingTerm (b i)))) =
              MvPolynomial.C cij *
                (Pij * ((b i - m.leadingTerm (b i)) * b j)) := by ring
            _ = 0 := by rw [hz, mul_zero]
        have hlt := coprime_sPolynomial_monomial_right_product_lt
          m (b i) (b j) (hmonic j)
          (m.degree (g i * b i) ⊔ m.degree (g j * b j) -
            m.degree (b i) ⊔ m.degree (b j))
          (m.leadingCoeff (g i) * m.leadingCoeff (g j))
          (by simpa only [ne_eq, mul_eq_zero, monomial_eq_zero,
                MonomialOrder.leadingCoeff_eq_zero_iff, not_or,
                hij, ↓reduceIte, hPij] using hterm)
        have hsuple :
            m.degree (b i) ⊔ m.degree (b j) ≤
              m.degree (g i * b i) ⊔ m.degree (g j * b j) := by
          apply sup_le_sup
          · rw [m.degree_mul
                (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hi).1)
                (hmonic i).ne_zero]
            exact self_le_add_left _ _
          · rw [m.degree_mul
                (Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hj).1)
                (hmonic j).ne_zero]
            exact self_le_add_left _ _
        have hsimpl :
            (m.degree (g i * b i) ⊔ m.degree (g j * b j) -
              m.degree (b i) ⊔ m.degree (b j)) +
                m.degree (b i) + m.degree (b j) =
              m.degree (g i * b i) ⊔ m.degree (g j * b j) := by
          have hbase := finsupp_sup_eq_add_of_disjoint_support
            (m.degree (b i)) (m.degree (b j)) (hdisjoint i j hij)
          rw [hbase] at hsuple ⊢
          simpa only [add_assoc] using tsub_add_cancel_of_le hsuple
        have htopij :
            m.toSyn
              (m.degree (g i * b i) ⊔ m.degree (g j * b j)) = d := by
          have hi' : m.degree (g i * b i) = m.toSyn.symm d := by
            apply m.toSyn.injective
            simpa only [AddEquiv.apply_symm_apply, mul_comm] using hpi
          have hj' : m.degree (g j * b j) = m.toSyn.symm d := by
            apply m.toSyn.injective
            simpa only [AddEquiv.apply_symm_apply, mul_comm] using hpj
          simp only [hi', hj', sup_idem, AddEquiv.apply_symm_apply]
        rw [hsimpl] at hlt
        have hscaled :
            m.toSyn (m.degree
              (Pij * ((b i - m.leadingTerm (b i)) * b j))) < d := by
          simpa [hPij, hij, htopij] using hlt
        have hc0 : cij ≠ 0 := by
          intro hz
          simp only [hz, zero_smul, mul_zero, not_true_eq_false] at hzero
        have hrewrite :
            b j * (cij • (Pij * (b i - m.leadingTerm (b i)))) =
              MvPolynomial.C cij *
                (Pij * ((b i - m.leadingTerm (b i)) * b j)) := by
          simp only [Algebra.smul_def, algebraMap_eq]
          ring
        rw [hrewrite, m.degree_mul
          (MvPolynomial.C_ne_zero.mpr hc0) hterm,
          m.degree_C, zero_add]
        exact hscaled

theorem buchberger_representation_improvement
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (hmonic : ∀ i : ι, m.Monic (b i))
    (hdisjoint : ∀ i j : ι, i ≠ j →
      Disjoint (m.degree (b i)).support (m.degree (b j)).support)
    (g : ι →₀ MvPolynomial σ K)
    (p : MvPolynomial σ K)
    (hrep : Finsupp.linearCombination (MvPolynomial σ K) b g = p)
    (hbad : m.toSyn (m.degree p) < representationDegree m b g)
    (hresidual :
      representationDegree m b
        (g - ∑ i ∈ g.support.filter
            (fun i => m.toSyn (m.degree (b i * g i)) =
              representationDegree m b g),
          Finsupp.single i (m.leadingTerm (g i))) <
        representationDegree m b g) :
    ∃ g' : ι →₀ MvPolynomial σ K,
      Finsupp.linearCombination (MvPolynomial σ K) b g' = p ∧
        representationDegree m b g' < representationDegree m b g := by
  classical
  let d : m.syn := representationDegree m b g
  let D : σ →₀ ℕ := m.toSyn.symm d
  let B : Finset ι := g.support.filter
    (fun i => m.toSyn (m.degree (b i * g i)) = d)
  have hd : (⊥ : m.syn) < d :=
    lt_of_le_of_lt bot_le hbad
  have hsum : (∑ i ∈ g.support, b i * g i) = p := by
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul, mul_comm] using hrep
  have htotal :
      m.toSyn (m.degree (∑ i ∈ g.support, b i * g i)) <
        m.toSyn D := by
    rw [hsum]
    simpa [D] using hbad
  have hbound : ∀ i ∈ g.support,
      m.toSyn (m.degree (b i * g i)) ≤ m.toSyn D := by
    intro i hi
    simpa [D, d] using
      degree_mul_le_representationDegree m b g i
        (Finsupp.mem_support_iff.mp hi)
  have htopcancel :
      m.toSyn (m.degree
        (∑ i ∈ B, m.leadingTerm (g i) * b i)) < d := by
    have hfilter :
        g.support.filter (fun i => m.degree (b i * g i) = D) = B := by
      ext i
      simp only [B, Finset.mem_filter]
      constructor
      · rintro ⟨hi, hdegree⟩
        refine ⟨hi, ?_⟩
        rw [hdegree]
        simp only [AddEquiv.apply_symm_apply, D]
      · rintro ⟨hi, hdegree⟩
        refine ⟨hi, ?_⟩
        apply m.toSyn.injective
        simpa [D] using hdegree
    simpa [hfilter, D] using
      top_leadingTerm_sum_degree_lt m b (fun i => g i)
        g.support D hbound htotal
  have htop : ∀ i ∈ B,
      m.toSyn (m.degree (m.leadingTerm (g i) * b i)) = d ∨
        m.leadingTerm (g i) * b i = 0 := by
    intro i hi
    left
    have hi' := (Finset.mem_filter.mp hi).2
    simpa only [mul_comm, MonomialOrder.degree_mul_leadingTerm] using hi'
  obtain ⟨c, hc⟩ := top_leading_multiple_sPolynomial_decomposition
    m B b (fun i => g i) d htop htopcancel
  let P : ι → ι → MvPolynomial σ K := fun i j =>
    if i = j then 0 else
      MvPolynomial.monomial
        (m.degree (g i * b i) ⊔ m.degree (g j * b j) -
          m.degree (b i) ⊔ m.degree (b j))
        (m.leadingCoeff (g i) * m.leadingCoeff (g j))
  have hreplace :
      (∑ i ∈ B, m.leadingTerm (g i) * b i) =
        ∑ i ∈ B, ∑ j ∈ B, c i j •
          (P i j * ((m.leadingTerm (b j) - b j) * b i +
            (b i - m.leadingTerm (b i)) * b j)) := by
    rw [hc]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · subst j
      simp only [Std.le_refl, sup_of_le_left, MonomialOrder.sPolynomial_self, mul_zero, smul_zero,
        ↓reduceIte, zero_mul, P]
    · rw [coprime_sPolynomial_eq m (b i) (b j)
        (hmonic i) (hmonic j) (hdisjoint i j hij)]
      simp only [hij, ↓reduceIte, P]
  let residual : ι →₀ MvPolynomial σ K :=
    g - ∑ i ∈ B, Finsupp.single i (m.leadingTerm (g i))
  let correction : ι → ι → ι →₀ MvPolynomial σ K := fun i j =>
    Finsupp.single i
      (c i j • (P i j * (m.leadingTerm (b j) - b j))) +
    Finsupp.single j
      (c i j • (P i j * (b i - m.leadingTerm (b i))))
  let g' : ι →₀ MvPolynomial σ K :=
    residual + ∑ i ∈ B, ∑ j ∈ B, correction i j
  refine ⟨g', ?_, ?_⟩
  · dsimp [g', residual, correction]
    rw [linearCombination_buchberger_reassembly m b g B c P hreplace,
      hrep]
  · apply representationDegree_add_sum_sum_lt
      m b residual B B correction d hd
    · simpa only using hresidual
    · intro i hi j hj
      dsimp [correction]
      obtain ⟨hleft, hright⟩ := buchberger_correction_pair_lt
        m b hmonic hdisjoint g d i j
        (by simpa only [B] using hi)
        (by simpa only [B] using hj)
        (P i j) (by rfl) (c i j)
      apply representationDegree_pair_lt m b i j
        (c i j • (P i j * (m.leadingTerm (b j) - b j)))
        (c i j • (P i j * (b i - m.leadingTerm (b i)))) d hd
      · exact hleft
      · exact hright

theorem buchberger_representation_improvement_of_monic
    {σ K ι : Type*} [Field K]
    (m : MonomialOrder σ)
    (b : ι → MvPolynomial σ K)
    (hmonic : ∀ i : ι, m.Monic (b i))
    (hdisjoint : ∀ i j : ι, i ≠ j →
      Disjoint (m.degree (b i)).support (m.degree (b j)).support)
    (g : ι →₀ MvPolynomial σ K)
    (p : MvPolynomial σ K)
    (hrep : Finsupp.linearCombination (MvPolynomial σ K) b g = p)
    (hbad : m.toSyn (m.degree p) < representationDegree m b g) :
    ∃ g' : ι →₀ MvPolynomial σ K,
      Finsupp.linearCombination (MvPolynomial σ K) b g' = p ∧
        representationDegree m b g' < representationDegree m b g := by
  classical
  let d : m.syn := representationDegree m b g
  let B : Finset ι := g.support.filter
    (fun i => m.toSyn (m.degree (b i * g i)) = d)
  have hd : (⊥ : m.syn) < d := lt_of_le_of_lt bot_le hbad
  have hb : ∀ i : ι, b i ≠ 0 := fun i => (hmonic i).ne_zero
  have hbound : ∀ i : ι,
      m.toSyn (m.degree (b i * g i)) ≤ d := by
    intro i
    exact degree_mul_le_representationDegree_all m b g i
  have hB : ∀ i : ι,
      i ∈ B ↔ g i ≠ 0 ∧ m.toSyn (m.degree (b i * g i)) = d := by
    intro i
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
  have hresidual :
      representationDegree m b
        (g - ∑ i ∈ B, Finsupp.single i (m.leadingTerm (g i))) < d :=
    representationDegree_strip_top_leading_terms_lt m b g B d hd hb hbound hB
  exact buchberger_representation_improvement m b hmonic hdisjoint g p hrep hbad
    (by simpa only [B, d] using hresidual)

theorem pairwise_coprime_monic_leadingDivisibility
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (fs : List (MvPolynomial σ K))
    (hmonic : ∀ f ∈ fs, m.Monic f)
    (hdisjoint : fs.Pairwise
      (fun f g => Disjoint (m.degree f).support (m.degree g).support)) :
    ∀ p : MvPolynomial σ K, p ∈ Ideal.ofList fs → p ≠ 0 →
      ∃ f ∈ fs, m.degree f ≤ m.degree p := by
  classical
  intro p hp hpzero
  let ι := {f : MvPolynomial σ K // f ∈ fs}
  let b : ι → MvPolynomial σ K := fun i => i.val
  have hbmonic : ∀ i : ι, m.Monic (b i) :=
    fun i => hmonic i.val i.property
  have hbzero : ∀ i : ι, b i ≠ 0 := fun i => (hbmonic i).ne_zero
  have hpair : ∀ i j : ι, i ≠ j →
      Disjoint (m.degree (b i)).support (m.degree (b j)).support := by
    intro i j hij
    apply hdisjoint.forall i.property j.property
    intro heq
    exact hij (Subtype.ext heq)
  have hrep : ∃ g : ι →₀ MvPolynomial σ K,
      Finsupp.linearCombination (MvPolynomial σ K) b g = p :=
    (mem_ofList_iff_exists_linearCombination fs p).mp hp
  obtain ⟨i, hi⟩ := exists_degree_le_of_representationImprovement
    m b hbzero p hpzero hrep
      (fun g hg hbad =>
        buchberger_representation_improvement_of_monic
          m b hbmonic hpair g p hg hbad)
  exact ⟨i.val, i.property, hi⟩

end HigherYoungCoprimeLeadingBuchberger

end

section


open scoped BigOperators MonomialOrder

namespace HigherYoungCoprimeLeadingRegularSequence

open MvPolynomial

theorem finsupp_le_add_of_disjoint_support
    {σ : Type*} {a b c : σ →₀ ℕ}
    (hdisjoint : Disjoint a.support b.support)
    (hle : a ≤ b + c) : a ≤ c := by
  intro k
  by_cases ha : a k = 0
  · simp only [ha, zero_le]
  · have hb : b k = 0 := by
      by_contra hb
      exact (Finset.disjoint_left.mp hdisjoint)
        (Finsupp.mem_support_iff.mpr ha)
        (Finsupp.mem_support_iff.mpr hb)
    simpa only [ge_iff_le, Finsupp.coe_add, Pi.add_apply, hb, zero_add] using hle k

private def IsLeadingGroebnerFamily
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ) (fs : List (MvPolynomial σ K)) : Prop :=
  ∀ p : MvPolynomial σ K, p ∈ Ideal.ofList fs → p ≠ 0 →
    ∃ f ∈ fs, m.degree f ≤ m.degree p

theorem linearCombination_mem_ofList
    {σ K ι : Type*} [Field K]
    (fs : List (MvPolynomial σ K))
    (b : ι → MvPolynomial σ K)
    (hb : ∀ i : ι, b i ∈ fs)
    (g : ι →₀ MvPolynomial σ K) :
    Finsupp.linearCombination (MvPolynomial σ K) b g ∈
      Ideal.ofList fs := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply (Ideal.ofList fs).sum_mem
  intro i _
  exact (Ideal.ofList fs).mul_mem_left (g i)
    (Ideal.subset_span (hb i))

theorem mem_of_mul_mem_of_disjoint_leading
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (fs : List (MvPolynomial σ K))
    (hmonic : ∀ g ∈ fs, m.Monic g)
    (hgroebner : IsLeadingGroebnerFamily m fs)
    (f : MvPolynomial σ K) (hf : m.Monic f)
    (hdisjoint : ∀ g ∈ fs,
      Disjoint (m.degree g).support (m.degree f).support)
    (p : MvPolynomial σ K)
    (hp : f * p ∈ Ideal.ofList fs) :
    p ∈ Ideal.ofList fs := by
  classical
  let B := {g : MvPolynomial σ K // g ∈ fs}
  have hunit : ∀ g : B, IsUnit (m.leadingCoeff g.val) := by
    intro g
    rw [(hmonic g.val g.property).leadingCoeff_eq_one]
    exact isUnit_one
  obtain ⟨a, r, hdecomposition, _, hremainder⟩ :=
    m.div (b := fun g : B => g.val) hunit p
  have hcombination :
      Finsupp.linearCombination (MvPolynomial σ K)
        (fun g : B => g.val) a ∈ Ideal.ofList fs :=
    linearCombination_mem_ofList fs (fun g : B => g.val)
      (fun g => g.property) a
  have hproduct : f * r ∈ Ideal.ofList fs := by
    have hsub := (Ideal.ofList fs).sub_mem hp
      ((Ideal.ofList fs).mul_mem_left f hcombination)
    simpa only [hdecomposition, mul_add, add_sub_cancel_left] using hsub
  by_cases hr : r = 0
  · simpa only [hdecomposition, hr, add_zero] using hcombination
  · have hfzero : f ≠ 0 := hf.ne_zero
    have hfrzero : f * r ≠ 0 := mul_ne_zero hfzero hr
    obtain ⟨g, hg, hdegree⟩ := hgroebner (f * r) hproduct hfrzero
    have hdividesRemainder : m.degree g ≤ m.degree r := by
      apply finsupp_le_add_of_disjoint_support (hdisjoint g hg)
      rwa [m.degree_mul hfzero hr] at hdegree
    exact (hremainder (m.degree r) (m.degree_mem_support hr)
      ⟨g, hg⟩ hdividesRemainder).elim

theorem mem_ideal_smul_top_iff {R : Type*} [CommRing R]
    (I : Ideal R) (p : R) :
    p ∈ (I • (⊤ : Submodule R R) : Submodule R R) ↔ p ∈ I := by
  rw [Ideal.smul_top_eq_map]
  simpa only using (show p ∈ Submodule.restrictScalars R (Ideal.map (algebraMap R R) I) ↔ p ∈ I
    by simp)

theorem mem_of_X_mul_mem_of_avoids_leading_support
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (fs : List (MvPolynomial σ K))
    (hmonic : ∀ g ∈ fs, m.Monic g)
    (hgroebner : IsLeadingGroebnerFamily m fs)
    (i : σ)
    (havoid : ∀ g ∈ fs, i ∉ (m.degree g).support)
    (p : MvPolynomial σ K)
    (hp : MvPolynomial.X i * p ∈ Ideal.ofList fs) :
    p ∈ Ideal.ofList fs := by
  apply mem_of_mul_mem_of_disjoint_leading m fs hmonic hgroebner
    (MvPolynomial.X i) m.monic_X
  · intro g hg
    rw [m.degree_X]
    simpa only [ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single,
      Finset.disjoint_singleton_right, Finsupp.mem_support_iff, Decidable.not_not] using havoid g hg
  · exact hp

theorem isWeaklyRegular_of_leadingGroebner_prefix
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (fs : List (MvPolynomial σ K))
    (hmonic : ∀ f ∈ fs, m.Monic f)
    (hpairwise : fs.Pairwise (fun f g =>
      Disjoint (m.degree f).support (m.degree g).support))
    (hgroebner : ∀ k : Fin fs.length,
      IsLeadingGroebnerFamily m (fs.take k.val)) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) fs := by
  apply (RingTheory.Sequence.isWeaklyRegular_iff_Fin _ _).mpr
  intro k
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  intro p hp
  apply (mem_ideal_smul_top_iff _ p).mpr
  apply mem_of_mul_mem_of_disjoint_leading m (fs.take k.val)
    (fun g hg => hmonic g (List.take_subset k.val fs hg))
    (hgroebner k) fs[k] (hmonic fs[k] (List.getElem_mem k.isLt))
  · intro g hg
    obtain ⟨j, hj, hjg⟩ := List.mem_take_iff_getElem.mp hg
    have hjk : j < k.val := lt_of_lt_of_le hj (min_le_left _ _)
    have hjlen : j < fs.length := lt_of_lt_of_le hj (min_le_right _ _)
    have h := (List.pairwise_iff_getElem.mp hpairwise)
      j k.val hjlen k.isLt hjk
    simpa only [Fin.getElem_fin, hjg] using h
  · exact (mem_ideal_smul_top_iff _ _).mp hp

theorem isWeaklyRegular_of_pairwise_disjoint_monic_leading
    {σ K : Type*} [Field K]
    (m : MonomialOrder σ)
    (fs : List (MvPolynomial σ K))
    (hmonic : ∀ f ∈ fs, m.Monic f)
    (hpairwise : fs.Pairwise (fun f g =>
      Disjoint (m.degree f).support (m.degree g).support)) :
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial σ K) fs := by
  apply isWeaklyRegular_of_leadingGroebner_prefix
    m fs hmonic hpairwise
  intro k
  exact
    HigherYoungCoprimeLeadingBuchberger.pairwise_coprime_monic_leadingDivisibility
      m (fs.take k.val)
      (fun f hf => hmonic f (List.take_subset k.val fs hf))
      (List.Pairwise.sublist (List.take_sublist k.val fs) hpairwise)

end HigherYoungCoprimeLeadingRegularSequence

end

section


open scoped BigOperators

namespace HigherHarmonicYoung

open ArbitraryRankMixedTraceRegularity
open MetricCodes.Spherical.HigherYoungCoprimeLeadingRegularSequence

theorem rowPairingPolynomial_swap {r n : ℕ}
    (i j : Fin (r + 1)) :
    rowPairingPolynomial (n := n) i j =
      rowPairingPolynomial (n := n) j i := by
  unfold rowPairingPolynomial
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem gramQuadraticList_ideal_eq_youngGramRadialIdeal
    (r n : ℕ) :
    Ideal.ofList (gramQuadraticList r n) =
      youngGramRadialIdeal r n := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le]
    intro p hp
    change p ∈ gramQuadraticList r n at hp
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hp
    exact rowPairingPolynomial_mem_youngGramRadialIdeal z.val.1 z.val.2
  · rw [youngGramRadialIdeal, Ideal.span_le]
    intro p hp
    obtain ⟨⟨i, j⟩, rfl⟩ := hp
    apply Ideal.subset_span
    by_cases hij : i ≤ j
    · let z : UpperGramPair r := ⟨(i, j), hij⟩
      change rowPairingPolynomial (n := n) i j ∈ gramQuadraticList r n
      apply List.mem_map.mpr
      refine ⟨z, ?_, rfl⟩
      simp only [Finset.mem_toList, Finset.mem_univ]
    · have hji : j ≤ i := le_of_not_ge hij
      let z : UpperGramPair r := ⟨(j, i), hji⟩
      change rowPairingPolynomial (n := n) i j ∈ gramQuadraticList r n
      rw [rowPairingPolynomial_swap]
      apply List.mem_map.mpr
      refine ⟨z, ?_, rfl⟩
      simp only [Finset.mem_toList, Finset.mem_univ]

theorem gramQuadraticList_weighted_monic
    {r n : ℕ} (hn : 2 * r < n)
    (p : PolynomialSpace r n)
    (hp : p ∈ gramQuadraticList r n) :
    (weightedMonomialOrder (gramVariableNatWeight r n)).Monic p := by
  unfold gramQuadraticList at hp
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hp
  exact gramPairPolynomial_weighted_monic hn z

theorem gramQuadraticList_weighted_degree_pairwise_disjoint
    {r n : ℕ} (hn : 2 * r < n) :
    (gramQuadraticList r n).Pairwise
      (fun p q => Disjoint
        ((weightedMonomialOrder (gramVariableNatWeight r n)).degree p).support
        ((weightedMonomialOrder (gramVariableNatWeight r n)).degree q).support) := by
  unfold gramQuadraticList
  rw [List.pairwise_map]
  apply (Finset.nodup_toList
    (Finset.univ : Finset (UpperGramPair r))).imp
  intro z w hzw
  exact gramPairPolynomial_weighted_degree_support_disjoint hn z w hzw

theorem gramQuadraticList_isWeaklyRegular
    {r n : ℕ} (hn : 2 * r < n) :
    RingTheory.Sequence.IsWeaklyRegular (PolynomialSpace r n)
      (gramQuadraticList r n) := by
  apply isWeaklyRegular_of_pairwise_disjoint_monic_leading
    (weightedMonomialOrder (gramVariableNatWeight r n))
    (gramQuadraticList r n)
  · exact gramQuadraticList_weighted_monic hn
  · exact gramQuadraticList_weighted_degree_pairwise_disjoint hn

end HigherHarmonicYoung

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungMixedGapBranching

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

theorem polarization_mem_youngGramRadialIdeal {r N : ℕ}
    (a b : Fin (r + 1)) {p : PolynomialSpace r N}
    (hp : p ∈ youngGramRadialIdeal r N) :
    polarization r N a b p ∈ youngGramRadialIdeal r N := by
  classical
  change p ∈ Submodule.span (PolynomialSpace r N)
    (Set.range fun ij : Fin (r + 1) × Fin (r + 1) =>
      rowPairingPolynomial (n := N) ij.1 ij.2) at hp
  induction hp using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hg
      rw [polarization_rowPairingPolynomial]
      split_ifs with hi hj
      · exact (youngGramRadialIdeal r N).add_mem
          (rowPairingPolynomial_mem_youngGramRadialIdeal a j)
          (rowPairingPolynomial_mem_youngGramRadialIdeal i a)
      · simpa only [add_zero] using rowPairingPolynomial_mem_youngGramRadialIdeal a j
      · simpa only [zero_add] using rowPairingPolynomial_mem_youngGramRadialIdeal i a
      · simp only [add_zero, zero_mem]
  | zero => simp only [map_zero, zero_mem]
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact (youngGramRadialIdeal r N).add_mem ihp ihq
  | smul c p hp ih =>
      change polarization r N a b (c * p) ∈ youngGramRadialIdeal r N
      rw [MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin.polarization_mul]
      apply (youngGramRadialIdeal r N).add_mem
      · exact (youngGramRadialIdeal r N).mul_mem_left
          (polarization r N a b c) (by
            exact hp)
      · exact (youngGramRadialIdeal r N).mul_mem_left c ih

end HigherYoungMixedGapBranching

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonGramIdeal

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherYoungMixedGapBranching
open MetricCodes.Spherical.HigherChannel

theorem lowerPolarizationPath_mem_youngGramRadialIdeal
    {r n : ℕ} (path : List (Fin (r + 1)))
    {p : PolynomialSpace r n}
    (hp : p ∈ youngGramRadialIdeal r n) :
    lowerPolarizationPath path p ∈ youngGramRadialIdeal r n := by
  induction path with
  | nil => exact hp
  | cons i rest ih =>
      cases rest with
      | nil => exact hp
      | cons j tail =>
          exact polarization_mem_youngGramRadialIdeal j i ih

theorem arbitraryRowAxialRaise_mem_youngGramRadialIdeal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    {p : PolynomialSpace r n}
    (hp : p ∈ youngGramRadialIdeal r n) :
    arbitraryRowAxialRaise lam row k p ∈ youngGramRadialIdeal r n := by
  classical
  rw [arbitraryRowAxialRaise_apply]
  apply Submodule.sum_mem
  intro S _
  rw [MvPolynomial.smul_eq_C_mul]
  exact (youngGramRadialIdeal r n).mul_mem_left _
    ((youngGramRadialIdeal r n).mul_mem_left _
      (lowerPolarizationPath_mem_youngGramRadialIdeal
        ((S.sort (· ≤ ·)) ++ [row]) hp))

theorem arbitraryRowAxialRaise_sub_mem_youngGramRadialIdeal
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p q : PolynomialSpace r n)
    (h : p - q ∈ youngGramRadialIdeal r n) :
    arbitraryRowAxialRaise lam row k p -
        arbitraryRowAxialRaise lam row k q ∈
      youngGramRadialIdeal r n := by
  rw [← map_sub]
  exact arbitraryRowAxialRaise_mem_youngGramRadialIdeal lam row k h

/-- The arbitrary row path weight used in the spherical-code argument. -/
def arbitraryRowPathWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    List (Fin (r + 1)) → (Fin (r + 1) → ℕ)
  | [] => lam
  | row :: rows => arbitraryRowPathWeight (raiseWeight lam row) rows

/-- The iterated arbitrary row axial raise used in the spherical-code argument. -/
def iteratedArbitraryRowAxialRaise {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (k : Fin n) :
    List (Fin (r + 1)) →
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
  | [] => LinearMap.id
  | row :: rows =>
      (iteratedArbitraryRowAxialRaise (raiseWeight lam row) k rows).comp
        (arbitraryRowAxialRaise lam row k)

theorem iteratedArbitraryRowAxialRaise_append
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (k : Fin n)
    (rows rows' : List (Fin (r + 1))) :
    iteratedArbitraryRowAxialRaise lam k (rows ++ rows') =
      (iteratedArbitraryRowAxialRaise
        (arbitraryRowPathWeight lam rows) k rows').comp
        (iteratedArbitraryRowAxialRaise lam k rows) := by
  induction rows generalizing lam with
  | nil => simp only [List.nil_append, arbitraryRowPathWeight, iteratedArbitraryRowAxialRaise,
             LinearMap.comp_id]
  | cons row rows ih =>
      simp only [List.cons_append, iteratedArbitraryRowAxialRaise,
        arbitraryRowPathWeight]
      rw [ih (raiseWeight lam row)]
      exact LinearMap.comp_assoc _ _ _

end ArbitraryRowMickelssonGramIdeal

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonWeightHomogeneity

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin

theorem lowerPolarizationPath_isHomogeneous
    {r n m : ℕ} (path : List (Fin (r + 1)))
    (p : PolynomialSpace r n) (hp : p.IsHomogeneous m) :
    (lowerPolarizationPath path p).IsHomogeneous m := by
  induction path with
  | nil => exact hp
  | cons i rest ih =>
      cases rest with
      | nil => exact hp
      | cons j tail =>
          exact polarization_isHomogeneous_harmonicLift
            j i (lowerPolarizationPath (j :: tail) p) ih

theorem arbitraryRowAxialRaise_isHomogeneous
    {r n m : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) (hp : p.IsHomogeneous m) :
    (arbitraryRowAxialRaise lam row k p).IsHomogeneous (m + 1) := by
  classical
  rw [arbitraryRowAxialRaise_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro S _
  rw [MvPolynomial.smul_eq_C_mul]
  simpa only [zero_add] using
    (MvPolynomial.isHomogeneous_C (Fin ((r + 1) * n)) (polarizationPathCoefficient lam row S)).mul
      (by
        simpa [Nat.add_comm] using
          (MvPolynomial.isHomogeneous_X ℝ (variableIndex (polarizationPathStart row S) k)).mul
            (lowerPolarizationPath_isHomogeneous ((S.sort (· ≤ ·)) ++ [row]) p hp))

theorem rowEuler_lowerPolarizationPath_append_singleton
    {r n : ℕ} (a target : Fin (r + 1))
    (rows : List (Fin (r + 1)))
    (p : PolynomialSpace r n) (c : ℝ)
    (hp : rowEuler r n a p = c • p) :
    rowEuler r n a
        (lowerPolarizationPath (rows ++ [target]) p) =
      c • lowerPolarizationPath (rows ++ [target]) p +
        (if a = target then
          lowerPolarizationPath (rows ++ [target]) p else 0) -
        (if a = rows.headD target then
          lowerPolarizationPath (rows ++ [target]) p else 0) := by
  induction rows with
  | nil =>
      simpa only [List.nil_append, lowerPolarizationPath, LinearMap.id_coe, id_eq, rowEuler_apply,
        List.headD_eq_head?_getD, List.head?_nil, Option.getD_none, add_sub_cancel_right] using hp
  | cons i tail ih =>
      cases tail with
      | nil =>
          change
            rowEuler r n a (polarization r n target i p) =
              c • polarization r n target i p +
                (if a = target then polarization r n target i p else 0) -
                (if a = i then polarization r n target i p else 0)
          rw [rowEuler_polarization_commutator, hp, map_smul]
      | cons j tail =>
          have ih' :
              rowEuler r n a
                (lowerPolarizationPath ((j :: tail) ++ [target]) p) =
                c • lowerPolarizationPath ((j :: tail) ++ [target]) p +
                  (if a = target then
                    lowerPolarizationPath ((j :: tail) ++ [target]) p
                    else 0) -
                  (if a = j then
                    lowerPolarizationPath ((j :: tail) ++ [target]) p
                    else 0) := by
            simpa only [List.cons_append, rowEuler_apply, List.headD_eq_head?_getD, List.head?_cons,
              Option.getD_some] using ih
          change
            rowEuler r n a
              (polarization r n j i
                (lowerPolarizationPath ((j :: tail) ++ [target]) p)) =
              c • polarization r n j i
                (lowerPolarizationPath ((j :: tail) ++ [target]) p) +
              (if a = target then
                polarization r n j i
                  (lowerPolarizationPath ((j :: tail) ++ [target]) p)
                else 0) -
              (if a = i then
                polarization r n j i
                  (lowerPolarizationPath ((j :: tail) ++ [target]) p)
                else 0)
          rw [rowEuler_polarization_commutator, ih',
            map_sub, map_add, map_smul]
          split_ifs <;>
            (try simp only [map_zero, add_zero,
              sub_zero]) <;> try abel

theorem sort_headD_eq_polarizationPathStart
    {r : ℕ} (row : Fin (r + 1))
    (S : Finset (Fin (r + 1))) :
    (S.sort (· ≤ ·)).headD row = polarizationPathStart row S := by
  classical
  by_cases hS : S.Nonempty
  · rw [polarizationPathStart, dite_eq_left hS]
    have hlength : 0 < (S.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      exact Finset.card_pos.mpr hS
    have hfirst := Finset.sorted_zero_eq_min'_aux S hlength hS
    cases hlist : S.sort (· ≤ ·) with
    | nil => simp only [hlist, List.length_nil, lt_self_iff_false] at hlength
    | cons i tail =>
        change i = S.min' hS
        simpa only [List.get_eq_getElem, hlist, List.getElem_cons_zero] using hfirst
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hempty, Finset.sort_empty, List.headD_eq_head?_getD, List.head?_nil,
      Option.getD_none, polarizationPathStart, Finset.not_nonempty_empty, ↓reduceDIte]

theorem rowEuler_axialCoordinate_lowerPolarizationPath
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a : Fin (r + 1)) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (p : PolynomialSpace r n)
    (hp : rowEuler r n a p = (lam a : ℝ) • p) :
    rowEuler r n a
        (MvPolynomial.X
          (variableIndex (polarizationPathStart row S) k) *
          lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p) =
      (raiseWeight lam row a : ℝ) •
        (MvPolynomial.X
          (variableIndex (polarizationPathStart row S) k) *
          lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p) := by
  have haxis :
      rowEuler r n a
        (MvPolynomial.X
          (variableIndex (polarizationPathStart row S) k)) =
        if a = polarizationPathStart row S then
          MvPolynomial.X (variableIndex a k) else 0 := by
    simpa only [polarization_self] using
      polarization_X_euler a a (polarizationPathStart row S) k
  rw [rowEuler_mul, haxis,
    rowEuler_lowerPolarizationPath_append_singleton
      a row (S.sort (· ≤ ·)) p (lam a) hp,
    sort_headD_eq_polarizationPathStart]
  by_cases harow : a = row
  · subst a
    by_cases hstart : row = polarizationPathStart row S
    · rw [← hstart]
      simp only [ite_true, raiseWeight, Function.update_self,
        Nat.cast_add, Nat.cast_one, MvPolynomial.smul_eq_C_mul,
        map_add, map_one]
      ring
    · simp only [hstart, ↓reduceIte, zero_mul, MvPolynomial.smul_eq_C_mul, map_natCast, sub_zero,
        zero_add, raiseWeight, Function.update_self, Nat.cast_add, Nat.cast_one, MvPolynomial.C_add,
        MvPolynomial.C_1]
      ring
  · by_cases hastart : a = polarizationPathStart row S
    · subst a
      have hstartrow : polarizationPathStart row S ≠ row := harow
      simp only [↓reduceIte, MvPolynomial.smul_eq_C_mul, map_natCast, hstartrow, add_zero,
        raiseWeight, ne_eq, not_false_eq_true, Function.update_of_ne]
      ring
    · simp only [hastart, ↓reduceIte, zero_mul, MvPolynomial.smul_eq_C_mul, map_natCast, harow,
        add_zero, sub_zero, zero_add, raiseWeight, ne_eq, not_false_eq_true, Function.update_of_ne]
      ring

theorem arbitraryRowAxialRaise_rowEuler
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n)
    (hp : ∀ a : Fin (r + 1),
      rowEuler r n a p = (lam a : ℝ) • p)
    (a : Fin (r + 1)) :
    rowEuler r n a (arbitraryRowAxialRaise lam row k p) =
      (raiseWeight lam row a : ℝ) •
        arbitraryRowAxialRaise lam row k p := by
  classical
  rw [arbitraryRowAxialRaise_apply, map_sum,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_smul,
    rowEuler_axialCoordinate_lowerPolarizationPath
      lam row a k S p (hp a), smul_comm]

theorem sum_raiseWeight
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) :
    (∑ a : Fin (r + 1), raiseWeight lam row a) =
      (∑ a : Fin (r + 1), lam a) + 1 := by
  classical
  unfold raiseWeight
  rw [Finset.sum_update_of_mem (Finset.mem_univ row)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.add_sum_erase
    (Finset.univ : Finset (Fin (r + 1))) lam
    (Finset.mem_univ row)
  omega

end ArbitraryRowMickelssonWeightHomogeneity

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowSameAxisSchedule

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranch
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem sum_arbitraryRowPathWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (rows : List (Fin (r + 1))) :
    (∑ i, arbitraryRowPathWeight lam rows i) =
      (∑ i, lam i) + rows.length := by
  induction rows generalizing lam with
  | nil => simp only [arbitraryRowPathWeight, List.length_nil, add_zero]
  | cons row rows ih =>
      simp only [arbitraryRowPathWeight, List.length_cons]
      rw [ih (raiseWeight lam row), sum_raiseWeight]
      omega

theorem iteratedArbitraryRowAxialRaise_rowEuler
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (k : Fin n)
    (rows : List (Fin (r + 1)))
    (p : PolynomialSpace r n)
    (hp : ∀ i : Fin (r + 1),
      rowEuler r n i p = (lam i : ℝ) • p)
    (i : Fin (r + 1)) :
    rowEuler r n i (iteratedArbitraryRowAxialRaise lam k rows p) =
      (arbitraryRowPathWeight lam rows i : ℝ) •
        iteratedArbitraryRowAxialRaise lam k rows p := by
  induction rows generalizing lam p with
  | nil => simpa only [iteratedArbitraryRowAxialRaise, LinearMap.id_coe, id_eq, rowEuler_apply,
             arbitraryRowPathWeight] using hp i
  | cons row rows ih =>
      change
        rowEuler r n i
          (iteratedArbitraryRowAxialRaise (raiseWeight lam row) k rows
            (arbitraryRowAxialRaise lam row k p)) =
          (arbitraryRowPathWeight (raiseWeight lam row) rows i : ℝ) •
            iteratedArbitraryRowAxialRaise (raiseWeight lam row) k rows
              (arbitraryRowAxialRaise lam row k p)
      exact ih (raiseWeight lam row)
        (arbitraryRowAxialRaise lam row k p)
        (arbitraryRowAxialRaise_rowEuler lam row k p hp)

theorem iteratedArbitraryRowAxialRaise_isHomogeneous
    {r n d : ℕ} (lam : Fin (r + 1) → ℕ) (k : Fin n)
    (rows : List (Fin (r + 1)))
    (p : PolynomialSpace r n) (hp : p.IsHomogeneous d) :
    (iteratedArbitraryRowAxialRaise lam k rows p).IsHomogeneous
      (d + rows.length) := by
  induction rows generalizing lam p d with
  | nil => simpa only [iteratedArbitraryRowAxialRaise, LinearMap.id_coe, id_eq, List.length_nil,
             add_zero] using hp
  | cons row rows ih =>
      change
        (iteratedArbitraryRowAxialRaise (raiseWeight lam row) k rows
          (arbitraryRowAxialRaise lam row k p)).IsHomogeneous
            (d + (rows.length + 1))
      have h := ih (raiseWeight lam row)
        (arbitraryRowAxialRaise lam row k p)
        (arbitraryRowAxialRaise_isHomogeneous lam row k p hp)
      convert h using 1 ; omega

end ArbitraryRowSameAxisSchedule

namespace ArbitraryRankInterlacingPolynomialSeed

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem arbitraryRowPathWeight_eq_foldl {r : ℕ}
    (weight : Fin (r + 1) → ℕ)
    (rows : List (Fin (r + 1))) :
    arbitraryRowPathWeight weight rows =
      rows.foldl (fun lam row => raiseWeight lam row) weight := by
  induction rows generalizing weight with
  | nil => rfl
  | cons row rows ih =>
      exact ih (raiseWeight weight row)

end ArbitraryRankInterlacingPolynomialSeed

namespace ArbitraryRankReverseInterlacingPolynomialSeed

open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInterlacingPolynomialSeed
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingGapSchedule
open MetricCodes.Spherical.HigherYoungArbitraryRankInterlacingLegalSchedule
open MetricCodes.Spherical.ThreeRowYoungBranching

theorem arbitraryRowPathWeight_reverseInterlacingRowSchedule {r : ℕ}
    {lam : Fin (r + 2) → ℕ} {mu : Fin (r + 1) → ℕ}
    (h : Interlaces lam mu) :
    arbitraryRowPathWeight (appendZeroWeight mu)
      (reverseInterlacingRowSchedule lam mu) = lam := by
  rw [arbitraryRowPathWeight_eq_foldl]
  exact foldl_reverseInterlacingRowSchedule_eq_target h

/-- The reverse interlacing polynomial seed used in the spherical-code argument. -/
def reverseInterlacingPolynomialSeed
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) mu →ₗ[ℝ]
      PolynomialSpace (r + 1) (n + 1) :=
  (iteratedArbitraryRowAxialRaise
    (appendZeroWeight mu) (Fin.last n)
    (reverseInterlacingRowSchedule lam mu)).comp
      ((harmonicYoungSubmodule (n := n + 1)
        (appendZeroWeight mu)).subtype.comp
          (terminalZeroSelectedBranchIsometry mu).toLinearMap)

theorem reverseInterlacingPolynomialSeed_rowEuler
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (p : HarmonicYoungSpace (n := n) mu)
    (i : Fin (r + 2)) :
    rowEuler (r + 1) (n + 1) i
      (reverseInterlacingPolynomialSeed lam mu p) =
      (lam i : ℝ) • reverseInterlacingPolynomialSeed lam mu p := by
  let q : HarmonicYoungSpace (n := n + 1)
      (appendZeroWeight mu) :=
    terminalZeroSelectedBranchIsometry mu p
  have heuler :=
    iteratedArbitraryRowAxialRaise_rowEuler
      (appendZeroWeight mu) (Fin.last n)
      (reverseInterlacingRowSchedule lam mu)
      (q : PolynomialSpace (r + 1) (n + 1))
      ((mem_harmonicYoungSubmodule (appendZeroWeight mu)
        (q : PolynomialSpace (r + 1) (n + 1))).mp q.property).2.1 i
  rw [arbitraryRowPathWeight_reverseInterlacingRowSchedule h] at heuler
  exact heuler

theorem reverseInterlacingPolynomialSeed_isHomogeneous
    {r n : ℕ} (lam : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (p : HarmonicYoungSpace (n := n) mu) :
    (reverseInterlacingPolynomialSeed lam mu p).IsHomogeneous
      (∑ i, lam i) := by
  let q : HarmonicYoungSpace (n := n + 1)
      (appendZeroWeight mu) :=
    terminalZeroSelectedBranchIsometry mu p
  have hdegree :=
    iteratedArbitraryRowAxialRaise_isHomogeneous
      (appendZeroWeight mu) (Fin.last n)
      (reverseInterlacingRowSchedule lam mu)
      (q : PolynomialSpace (r + 1) (n + 1))
      ((mem_harmonicYoungSubmodule (appendZeroWeight mu)
        (q : PolynomialSpace (r + 1) (n + 1))).mp q.property).1
  have hsum := sum_arbitraryRowPathWeight (appendZeroWeight mu)
    (reverseInterlacingRowSchedule lam mu)
  rw [arbitraryRowPathWeight_reverseInterlacingRowSchedule h] at hsum
  rw [hsum]
  exact hdegree

end ArbitraryRankReverseInterlacingPolynomialSeed

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonHighest

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching

theorem polarization_lowerPolarizationPath_commute_tail
    {r n : ℕ} (row a b : Fin (r + 1))
    (hrow : row ≤ a) (hab : a < b)
    (path : List (Fin (r + 1)))
    (hpath : ∀ i ∈ path, i ≤ row)
    (hordered : path.Pairwise (· < ·))
    (p : PolynomialSpace r n) :
    polarization r n a b (lowerPolarizationPath path p) =
      lowerPolarizationPath path (polarization r n a b p) := by
  induction path generalizing p with
  | nil => rfl
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          have hpair := (List.pairwise_cons.mp hordered)
          have hij : i < j := hpair.1 j (by simp only [List.mem_cons, true_or])
          have hjrow : j ≤ row := hpath j (by simp only [List.mem_cons, true_or, or_true])
          have hbj : b ≠ j := by
            intro h
            have hja : j ≤ a := hjrow.trans hrow
            subst b
            exact (not_lt_of_ge hja) hab
          have hia : i ≠ a := by
            intro h
            have hile : i < a := hij.trans_le (hjrow.trans hrow)
            exact (ne_of_lt hile) h
          change
            polarization r n a b
                (polarization r n j i
                  (lowerPolarizationPath (j :: tail) p)) =
              polarization r n j i
                (lowerPolarizationPath (j :: tail)
                  (polarization r n a b p))
          rw [polarization_polarization_commutator]
          simp only [ite_eq_right hbj, ite_eq_right hia, add_zero, sub_zero]
          congr 1
          apply ih
          · intro z hz
            exact hpath z (by simp only [List.mem_cons, hz, or_true])
          · exact hpair.2

theorem sortedPolarizationPath_pairwise
    {r : ℕ} (row : Fin (r + 1))
    (S : Finset (Fin (r + 1)))
    (hsub : S ⊆ precedingRows row) :
    ((S.sort (· ≤ ·)) ++ [row]).Pairwise (· < ·) := by
  have hle := Finset.pairwise_sort S (· ≤ ·)
  have hne := List.nodup_iff_pairwise_ne.mp
    (Finset.sort_nodup S (· ≤ ·))
  have hstrict : (S.sort (· ≤ ·)).Pairwise (· < ·) :=
    (hle.and hne).imp fun h => lt_of_le_of_ne h.1 h.2
  apply List.pairwise_append.mpr
  refine ⟨hstrict, by simp only [List.pairwise_cons, List.not_mem_nil, IsEmpty.forall_iff,
                        implies_true, List.Pairwise.nil, and_self], ?_⟩
  intro i hi j hj
  have hj' : j = row := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hj
  subst j
  exact (mem_precedingRows i row).mp
    (hsub ((Finset.mem_sort (· ≤ ·)).mp hi))

theorem sortedPolarizationPath_le_row
    {r : ℕ} (row : Fin (r + 1))
    (S : Finset (Fin (r + 1)))
    (hsub : S ⊆ precedingRows row)
    (i : Fin (r + 1))
    (hi : i ∈ (S.sort (· ≤ ·)) ++ [row]) :
    i ≤ row := by
  rcases (List.mem_append.mp hi) with hi | hi
  · exact le_of_lt ((mem_precedingRows i row).mp
      (hsub ((Finset.mem_sort (· ≤ ·)).mp hi)))
  · have : i = row := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hi
    simp [this]

theorem polarizationPathStart_le_row
    {r : ℕ} (row : Fin (r + 1))
    (S : Finset (Fin (r + 1)))
    (hsub : S ⊆ precedingRows row) :
    polarizationPathStart row S ≤ row := by
  by_cases hS : S.Nonempty
  · exact le_of_lt
      (polarizationPathStart_lt_of_nonempty row S hS hsub)
  · have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hzero, polarizationPathStart_empty, Std.le_refl]

theorem arbitraryRowAxialRaise_polarization_tail
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1)) (k : Fin n)
    (hrow : row ≤ a) (hab : a < b)
    (p : PolynomialSpace r n)
    (hhighest : ∀ i j : Fin (r + 1), i < j →
      polarization r n i j p = 0) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) = 0 := by
  classical
  rw [arbitraryRowAxialRaise_apply, map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  have hsub : S ⊆ precedingRows row := Finset.mem_powerset.mp hS
  have hstart : polarizationPathStart row S ≤ row :=
    polarizationPathStart_le_row row S hsub
  have hne : b ≠ polarizationPathStart row S := by
    intro heq
    have hba : b ≤ a := by
      rw [heq]
      exact hstart.trans hrow
    exact (not_lt_of_ge hba) hab
  rw [map_smul]
  change
    polarizationPathCoefficient lam row S •
      polarization r n a b
        (MvPolynomial.X (variableIndex (polarizationPathStart row S) k) *
          lowerPolarizationPath ((S.sort (· ≤ ·)) ++ [row]) p) = 0
  rw [polarization_mul_euler, polarization_X_euler, ite_eq_right hne,
    zero_mul, zero_add,
    polarization_lowerPolarizationPath_commute_tail row a b hrow hab
      ((S.sort (· ≤ ·)) ++ [row])
      (sortedPolarizationPath_le_row row S hsub)
      (sortedPolarizationPath_pairwise row S hsub),
    hhighest a b hab, map_zero, mul_zero, smul_zero]

theorem arbitraryRowAxialRaise_polarization_of_initial_simpleRoots
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n)
    (hhighest : ∀ i j : Fin (r + 1), i < j →
      polarization r n i j p = 0)
    (hsimple : ∀ a : Fin r, a.castSucc < row →
      polarization r n a.castSucc a.succ
        (arbitraryRowAxialRaise lam row k p) = 0)
    (a b : Fin (r + 1)) (hab : a < b) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) = 0 := by
  apply polarization_eq_zero_of_simpleRoots
    (arbitraryRowAxialRaise lam row k p) (i := a) (j := b) _ hab
  intro c
  by_cases hc : c.castSucc < row
  · exact hsimple c hc
  · apply arbitraryRowAxialRaise_polarization_tail lam row
      c.castSucc c.succ k (le_of_not_gt hc)
    · change c.val < c.val + 1
      omega
    · exact hhighest

end ArbitraryRowMickelssonHighest

end

section


open scoped BigOperators InnerProductSpace

namespace ArbitraryRowMickelssonSimpleRoot

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator

theorem simpleRoot_laterLower_of_highest
    {r n : ℕ} (a b j : Fin (r + 1))
    (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b (polarization r n j b q) = 0 := by
  rw [polarization_polarization_commutator, hq, map_zero]
  have hbj' : b ≠ j := ne_of_lt hbj
  have hba : b ≠ a := (ne_of_lt hab).symm
  simp only [hbj', ↓reduceIte, add_zero, hba, sub_self]

theorem simpleRoot_incomingLower_of_highest
    {r n : ℕ} (i a b : Fin (r + 1))
    (hia : i < a)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b (polarization r n b i q) =
      polarization r n a i q := by
  rw [polarization_polarization_commutator, hq, map_zero]
  have hia' : i ≠ a := ne_of_lt hia
  simp only [↓reduceIte, polarization_apply, zero_add, hia', sub_zero]

theorem simpleRoot_outgoingLower_of_highest
    {r n : ℕ} (a b j : Fin (r + 1))
    (hbj : b < j)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b (polarization r n j a q) =
      -polarization r n j b q := by
  rw [polarization_polarization_commutator, hq, map_zero]
  have hbj' : b ≠ j := ne_of_lt hbj
  simp only [hbj', ↓reduceIte, add_zero, polarization_apply, zero_sub]

theorem simpleRoot_path_neither
    {r n : ℕ} (i a b j : Fin (r + 1))
    (hia : i < a) (hbj : b < j)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b (polarization r n j i q) = 0 := by
  rw [polarization_polarization_commutator, hq, map_zero]
  have hbj' : b ≠ j := ne_of_lt hbj
  have hia' : i ≠ a := ne_of_lt hia
  simp only [hbj', ↓reduceIte, add_zero, hia', sub_self]

theorem simpleRoot_oppositeLaterLower_of_highest
    {r n : ℕ} (a b j : Fin (r + 1))
    (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n) (A B : ℝ)
    (hq : polarization r n a b q = 0)
    (hqa : rowEuler r n a q = A • q)
    (hqb : rowEuler r n b q = B • q) :
    polarization r n a b
        (polarization r n b a (polarization r n j b q)) =
      (A - B + 1) • polarization r n j b q := by
  have htail : polarization r n a b (polarization r n j b q) = 0 :=
    simpleRoot_laterLower_of_highest a b j hab hbj q hq
  have hja : a ≠ j := ne_of_lt (hab.trans hbj)
  have hba : a ≠ b := ne_of_lt hab
  have hbj' : b ≠ j := ne_of_lt hbj
  have ha :
      rowEuler r n a (polarization r n j b q) =
        A • polarization r n j b q := by
    rw [rowEuler_polarization_commutator, hqa, map_smul]
    simp only [polarization_apply, hja, ↓reduceIte, add_zero, hba, sub_zero]
  have hb :
      rowEuler r n b (polarization r n j b q) =
        B • polarization r n j b q - polarization r n j b q := by
    rw [rowEuler_polarization_commutator, hqb, map_smul]
    simp only [polarization_apply, hbj', ↓reduceIte, add_zero]
  rw [polarization_polarization_commutator, htail, map_zero]
  simp only [ite_true, zero_add, polarization_self]
  rw [ha, hb]
  simp only [polarization_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub,
    MvPolynomial.C_1]
  ring

theorem simpleRoot_path_first_only
    {r n : ℕ} (i a b j : Fin (r + 1))
    (hia : i < a) (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b
        (polarization r n a i (polarization r n j a q)) =
      -polarization r n a i (polarization r n j b q) := by
  rw [polarization_polarization_commutator]
  have hba : b ≠ a := (ne_of_lt hab).symm
  have hia' : i ≠ a := ne_of_lt hia
  simp only [ite_eq_right hba, ite_eq_right hia', add_zero, sub_zero]
  rw [simpleRoot_outgoingLower_of_highest a b j hbj q hq,
    map_neg]

theorem simpleRoot_path_second_only
    {r n : ℕ} (i a b j : Fin (r + 1))
    (hia : i < a) (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b
        (polarization r n b i (polarization r n j b q)) =
      polarization r n a i (polarization r n j b q) := by
  exact simpleRoot_incomingLower_of_highest i a b hia
    (polarization r n j b q)
    (simpleRoot_laterLower_of_highest a b j hab hbj q hq)

theorem simpleRoot_path_both
    {r n : ℕ} (i a b j : Fin (r + 1))
    (hia : i < a) (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n) (A B : ℝ)
    (hq : polarization r n a b q = 0)
    (hqa : rowEuler r n a q = A • q)
    (hqb : rowEuler r n b q = B • q) :
    polarization r n a b
        (polarization r n a i
          (polarization r n b a (polarization r n j b q))) =
      (A - B + 1) •
        polarization r n a i (polarization r n j b q) := by
  rw [polarization_polarization_commutator]
  have hba : b ≠ a := (ne_of_lt hab).symm
  have hia' : i ≠ a := ne_of_lt hia
  simp only [ite_eq_right hba, ite_eq_right hia', add_zero, sub_zero]
  rw [simpleRoot_oppositeLaterLower_of_highest
    a b j hab hbj q A B hq hqa hqb, map_smul]

theorem simpleRoot_coordinate_first_only
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex a k) *
          polarization r n j a q) =
      -(MvPolynomial.X (variableIndex a k) *
        polarization r n j b q) := by
  rw [polarization_mul_euler, polarization_X_euler]
  have hba : b ≠ a := (ne_of_lt hab).symm
  simp only [ite_eq_right hba, zero_mul, zero_add]
  rw [simpleRoot_outgoingLower_of_highest a b j hbj q hq,
    mul_neg]

theorem simpleRoot_coordinate_second_only
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n)
    (hq : polarization r n a b q = 0) :
    polarization r n a b
        (MvPolynomial.X (variableIndex b k) *
          polarization r n j b q) =
      MvPolynomial.X (variableIndex a k) *
        polarization r n j b q := by
  rw [polarization_mul_euler, polarization_X_euler]
  simp only [ite_true]
  rw [simpleRoot_laterLower_of_highest a b j hab hbj q hq]
  simp only [polarization_apply, mul_zero, add_zero]

theorem simpleRoot_coordinate_both
    {r n : ℕ} (a b j : Fin (r + 1)) (k : Fin n)
    (hab : a < b) (hbj : b < j)
    (q : PolynomialSpace r n) (A B : ℝ)
    (hq : polarization r n a b q = 0)
    (hqa : rowEuler r n a q = A • q)
    (hqb : rowEuler r n b q = B • q) :
    polarization r n a b
        (MvPolynomial.X (variableIndex a k) *
          polarization r n b a (polarization r n j b q)) =
      (A - B + 1) •
        (MvPolynomial.X (variableIndex a k) *
          polarization r n j b q) := by
  rw [polarization_mul_euler, polarization_X_euler]
  have hba : b ≠ a := (ne_of_lt hab).symm
  simp only [ite_eq_right hba, zero_mul, zero_add]
  rw [simpleRoot_oppositeLaterLower_of_highest
    a b j hab hbj q A B hq hqa hqb]
  simp only [polarization_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.C_add, MvPolynomial.C_sub,
    MvPolynomial.C_1]
  ring

end ArbitraryRowMickelssonSimpleRoot

end

end HigherHarmonicYoung

end Spherical

end MetricCodes

end MetricCodesNoncomputable
