/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.Nullstellensatz
import LeanPool.Stafford38.Stafford38.Geometry.ScalarExtensionPoints

/-!
# Scalar extension of equation-conormal vanishing
-/

namespace Stafford38.Geometry.ConormalScalarExtensionVanishing

open Stafford38.Geometry.AffineConormalClosure
open Stafford38.Geometry.AffineConormalSpan
open Stafford38.Geometry.CoisotropicTranslation
open Stafford38.Geometry.ScalarExtensionPoints
open Stafford38.Characteristic

noncomputable section

variable {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
variable {n : ℕ}

/-- The extended-field span of gradients of ground-field equations at the chosen point. -/
def groundGradientSpan (I : Ideal (MvPolynomial (Fin n) k))
    (y : Fin n → K) : Submodule K (Fin n → K) :=
  Submodule.span K
    (Set.range fun h : I => fun i =>
      MvPolynomial.eval₂ (algebraMap k K) y (MvPolynomial.pderiv i h.1))

omit [IsAlgClosed k] in
theorem differential_mem_groundGradientSpan
    (I : Ideal (MvPolynomial (Fin n) k)) (y : Fin n → K)
    (hy : ∀ h ∈ I, MvPolynomial.eval₂ (algebraMap k K) y h = 0)
    (g : MvPolynomial (Fin n) K)
    (hg : g ∈ I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) :
    (fun i => differentialAt y g i) ∈ groundGradientSpan I y := by
  classical
  change g ∈ Ideal.span
    (scalarPolynomialMap (k := k) (K := K) (Fin n) '' I) at hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨h, hh, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨⟨h, hh⟩, ?_⟩
      funext i
      exact (differentialAt_scalarPolynomialMap y h i).symm
  | zero =>
      change (0 : Fin n → K) ∈ groundGradientSpan I y
      exact (groundGradientSpan I y).zero_mem
  | add g h _ _ hg hh =>
      have heq : (fun i => differentialAt y (g + h) i) =
          (fun i => differentialAt y g i) + (fun i => differentialAt y h i) := by
        funext i
        simp [differentialAt]
      rw [heq]
      exact (groundGradientSpan I y).add_mem hg hh
  | smul a g hg ih =>
      have hgeval : MvPolynomial.eval y g = 0 := by
        have hy' : y ∈ MvPolynomial.zeroLocus K
            (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n))) :=
          (mem_zeroLocus_map_iff I y).mpr hy
        exact hy' g hg
      have heq : (fun i => differentialAt y (a * g) i) =
          MvPolynomial.eval y a • (fun i => differentialAt y g i) := by
        funext i
        simp [differentialAt,  hgeval]
      rw [smul_eq_mul, heq]
      exact (groundGradientSpan I y).smul_mem _ ih

omit [IsAlgClosed k] in
theorem conormal_covector_mem_groundGradientSpan
    (I : Ideal (MvPolynomial (Fin n) k)) (q : PhaseVar n → K)
    (hq : q ∈ equationConormalLocus
      (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n)))) :
    (fun i => q (.inr i)) ∈ groundGradientSpan I (fun i => q (.inl i)) := by
  classical
  let y : Fin n → K := fun i => q (.inl i)
  let ξ : Fin n → K := fun i => q (.inr i)
  have hq' := (mem_equationConormalLocus_map_iff I q).mp hq
  obtain ⟨c, hc⟩ := coordinate_mem_affineConormalSpace_exists_finsupp
    y ξ _ hq'.2
  have heq : ξ = ∑ g ∈ c.support, c g • (fun i => differentialAt y g.1 i) := by
    funext i
    simpa [Finset.sum_apply] using (hc i)
  change ξ ∈ groundGradientSpan I y
  rw [heq]
  apply Submodule.sum_mem
  intro g hg
  exact (groundGradientSpan I y).smul_mem _
    (differential_mem_groundGradientSpan I y hq'.1 g.1 g.2)

omit [IsAlgClosed k] in
theorem exists_ground_gradient_finsupp
    (I : Ideal (MvPolynomial (Fin n) k)) (q : PhaseVar n → K)
    (hq : q ∈ equationConormalLocus
      (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n)))) :
    ∃ c : I →₀ K, ∀ i,
      q (.inr i) = ∑ h ∈ c.support, c h *
        MvPolynomial.eval₂ (algebraMap k K) (fun j => q (.inl j))
          (MvPolynomial.pderiv i h.1) := by
  classical
  have hm := conormal_covector_mem_groundGradientSpan I q hq
  rw [groundGradientSpan, Finsupp.mem_span_range_iff_exists_finsupp] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨c, fun i => ?_⟩
  have hi := congrFun hc i
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, mul_comm] using hi.symm

/-- Substitution of a formal linear combination of finitely many equation gradients for the
fibre variables. -/
def finiteGradientSubstitution {ι : Type*} [Fintype ι]
    (h : ι → MvPolynomial (Fin n) k) :
    SymbolRing k n →+* MvPolynomial (Fin n ⊕ ι) k :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun i => MvPolynomial.X (.inl i))
      (fun i => ∑ a : ι, MvPolynomial.X (.inr a) *
        MvPolynomial.rename Sum.inl (MvPolynomial.pderiv i (h a))))

omit [IsAlgClosed k] in
theorem eval₂_finiteGradientSubstitution {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} [Fintype ι] (h : ι → MvPolynomial (Fin n) k)
    (P : SymbolRing k n) (z : Fin n ⊕ ι → L) :
    MvPolynomial.eval₂ (algebraMap k L) z (finiteGradientSubstitution h P) =
      MvPolynomial.eval₂ (algebraMap k L)
        (Sum.elim (fun i => z (.inl i))
          (fun i => ∑ a : ι, z (.inr a) *
            MvPolynomial.eval₂ (algebraMap k L) (fun j => z (.inl j))
              (MvPolynomial.pderiv i (h a)))) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [finiteGradientSubstitution]
  | add P Q hP hQ =>
      simp only [map_add, MvPolynomial.eval₂_add]
      rw [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, MvPolynomial.eval₂_mul]
      rw [hP]
      rcases i with i | i
      · simp [finiteGradientSubstitution]
      · simp? [finiteGradientSubstitution, MvPolynomial.eval₂_rename]
        left
        congr 1

theorem scalarExtension_vanishing
    (I : Ideal (MvPolynomial (Fin n) k)) (P : SymbolRing k n)
    (hP : ∀ q ∈ equationConormalLocus I, MvPolynomial.eval q P = 0)
    (q : PhaseVar n → K)
    (hq : q ∈ equationConormalLocus
      (I.map (scalarPolynomialMap (k := k) (K := K) (Fin n)))) :
    MvPolynomial.eval₂ (algebraMap k K) q P = 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_ground_gradient_finsupp I q hq
  let ι := {h : I // h ∈ c.support}
  let equations : ι → MvPolynomial (Fin n) k := fun a => a.1.1
  let ρ := finiteGradientSubstitution equations
  let J : Ideal (MvPolynomial (Fin n ⊕ ι) k) :=
    I.map (MvPolynomial.rename Sum.inl)
  have hvan : ρ P ∈ MvPolynomial.vanishingIdeal k
      (MvPolynomial.zeroLocus k J) := by
    rw [MvPolynomial.mem_vanishingIdeal_iff]
    intro z hz
    let y : Fin n → k := fun i => z (.inl i)
    let ξ : Fin n → k := fun i => ∑ a : ι, z (.inr a) * differentialAt y (equations a) i
    have hy : y ∈ MvPolynomial.zeroLocus k I := by
      intro f hf
      have hm : MvPolynomial.rename Sum.inl f ∈ J :=
        Ideal.mem_map_of_mem (MvPolynomial.rename Sum.inl) hf
      have := hz _ hm
      change MvPolynomial.eval₂ (algebraMap k k) z
        (MvPolynomial.rename Sum.inl f) = 0 at this
      rw [MvPolynomial.eval₂_rename] at this
      have he : z ∘ Sum.inl = y := by rfl
      rw [he] at this
      simpa [MvPolynomial.aeval_def] using this
    have hξ : coordinateCovector ξ ∈ affineConormalSpace y I := by
      rw [affineConormalSpace_eq_equationCovectorSpan]
      have heq : coordinateCovector ξ =
          ∑ a : ι, z (.inr a) • differentialCovector y (equations a) := by
        ext v
        simp? [ξ, coordinateCovector, differentialCovector,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp [mul_assoc]
      rw [heq]
      apply Submodule.sum_mem
      intro a ha
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨a.1, rfl⟩
    have heval := eval₂_finiteGradientSubstitution equations P z
    have hzero := hP (Sum.elim y ξ) ⟨hy, hξ⟩
    simpa [ρ, y, ξ, MvPolynomial.aeval_def] using heval.trans hzero
  let : Finite ι := Finite.of_fintype ι
  have hrad : ρ P ∈ J.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) J]
    exact hvan
  obtain ⟨m, hm⟩ := (Ideal.mem_radical_iff.mp hrad)
  let z : Fin n ⊕ ι → K := Sum.elim (fun i => q (.inl i)) (fun a => c a.1)
  have hzJ : z ∈ MvPolynomial.zeroLocus K J := by
    change z ∈ MvPolynomial.zeroLocus K
      (I.map (MvPolynomial.rename Sum.inl))
    rw [Ideal.map, MvPolynomial.zeroLocus_span]
    rintro _ ⟨f, hf, rfl⟩
    change MvPolynomial.eval₂ (algebraMap k K) z
      (MvPolynomial.rename Sum.inl f) = 0
    rw [MvPolynomial.eval₂_rename]
    have he : z ∘ Sum.inl = fun i => q (.inl i) := by
      funext i
      rfl
    rw [he]
    exact ((mem_equationConormalLocus_map_iff I q).mp hq).1 f hf
  have hpw : (MvPolynomial.eval₂ (algebraMap k K) z (ρ P)) ^ m = 0 := by
    simpa only [MvPolynomial.aeval_def, map_pow] using hzJ _ hm
  have hrho : MvPolynomial.eval₂ (algebraMap k K) z (ρ P) = 0 :=
    eq_zero_of_pow_eq_zero hpw
  rw [eval₂_finiteGradientSubstitution equations P z] at hrho
  have hpoint :
      Sum.elim (fun i => z (.inl i))
        (fun i => ∑ a : ι, z (.inr a) *
          MvPolynomial.eval₂ (algebraMap k K) (fun j => z (.inl j))
            (MvPolynomial.pderiv i (equations a))) = q := by
    funext v
    rcases v with i | i
    · rfl
    · have hi := (hc i).symm
      rw [← Finset.sum_attach] at hi
      simpa [z, equations, ι, Finsupp.sum] using hi
  rw [hpoint] at hrho
  exact hrho


end
end Stafford38.Geometry.ConormalScalarExtensionVanishing
