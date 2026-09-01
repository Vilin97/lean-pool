/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Analytic.ConstantRank
import LeanPool.LocalComplexGeometry.FiniteProjection.Main
import LeanPool.LocalComplexGeometry.Noetherian.Ruckert
import LeanPool.LocalComplexGeometry.Nullstellensatz.Main

/-!
# Palomar-facing theorem surface

The theorem statements in this module use only Mathlib objects and the
elementary definition of a holomorphic germ.  The implementation-specific
coordinate, quotient-basis, and local-biholomorphism structures remain in the
proof development and are eliminated from the public statement surface.
-/

open Filter
open scoped BigOperators Topology


namespace LocalComplexGeometry

noncomputable section

/-- **Ruckert's basis theorem.** The analytic function-germ ring is
Noetherian in every finite complex dimension.  The ring is defined locally in
the statement so the compared type contains only Mathlib constants. -/
theorem holomorphicGerm_isNoetherian (n : ℕ) :
    let O (k : ℕ) :
        Subring (Filter.Germ (nhds (0 : Fin k → ℂ)) ℂ) :=
      { carrier := {phi | ∃ f : (Fin k → ℂ) → ℂ,
          AnalyticAt ℂ f 0 ∧
            (f : Filter.Germ (nhds (0 : Fin k → ℂ)) ℂ) = phi}
        zero_mem' := ⟨0, analyticAt_const, rfl⟩
        one_mem' := ⟨1, analyticAt_const, rfl⟩
        add_mem' := by
          rintro phi psi ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
          exact ⟨f + g, hf.add hg, by simp⟩
        mul_mem' := by
          rintro phi psi ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
          exact ⟨f * g, hf.mul hg, by simp⟩
        neg_mem' := by
          rintro phi ⟨f, hf, rfl⟩
          exact ⟨-f, hf.neg, by simp⟩ }
    IsNoetherianRing (O n) := by
  change IsNoetherianRing (HolomorphicGerm n)
  exact holomorphicGerm_isNoetherian_core n

/-- A statement-only formulation of the explicit rank-`d` power basis in a
hypersurface quotient. -/
private def HasUniquePowerExpansion {n : ℕ}
    (f : HolomorphicGerm (n + 1)) (d : ℕ) : Prop :=
  let I : Ideal (HolomorphicGerm (n + 1)) :=
    Ideal.span ({f} : Set (HolomorphicGerm (n + 1)))
  letI : I.IsTwoSided := Ideal.instIsTwoSided_1 I
  let q := Ideal.Quotient.mk I
  ∃ (ι : HolomorphicGerm n →+* HolomorphicGerm (n + 1))
      (w : HolomorphicGerm (n + 1)),
    (∀ (a : HolomorphicGerm n) (A : ComplexEuclidean n → ℂ),
      AnalyticAt ℂ A 0 →
      (A : FunctionGerm n) = (a : FunctionGerm n) →
      ((fun x : ComplexEuclidean (n + 1) ↦
          A (fun i ↦ x i.castSucc)) : FunctionGerm (n + 1)) =
        (ι a : FunctionGerm (n + 1))) ∧
    (((fun x : ComplexEuclidean (n + 1) ↦ x (Fin.last n)) :
        ComplexEuclidean (n + 1) → ℂ) : FunctionGerm (n + 1)) =
      (w : FunctionGerm (n + 1)) ∧
    ∀ y : HolomorphicGerm (n + 1) ⧸ I,
      ∃! c : Fin d → HolomorphicGerm n,
        y = ∑ i, q (ι (c i) * w ^ (i : ℕ))

/-- The basis-valued result gives unique coefficients for every class in the
hypersurface quotient. -/
private theorem hasUniquePowerExpansion_of_isFiniteFreeOfRankOverBase
    {n d : ℕ} {f : HolomorphicGerm (n + 1)}
    (h : IsFiniteFreeOfRankOverBase f d) :
    HasUniquePowerExpansion f d := by
  classical
  unfold IsFiniteFreeOfRankOverBase at h
  dsimp only at h
  obtain ⟨b, hb⟩ := h
  let I : Ideal (HolomorphicGerm (n + 1)) :=
    Ideal.span ({f} : Set (HolomorphicGerm (n + 1)))
  let : I.IsTwoSided := Ideal.instIsTwoSided_1 I
  let q := Ideal.Quotient.mk I
  let : Algebra (HolomorphicGerm n) (HolomorphicGerm (n + 1) ⧸ I) :=
    ((q.comp (lowerDimensionalInclusion n))).toAlgebra
  unfold HasUniquePowerExpansion
  dsimp only
  refine ⟨lowerDimensionalInclusion n, lastCoordinateGerm n, ?_, ?_, ?_⟩
  · intro a A hA hAa
    change ((fun x : ComplexEuclidean (n + 1) ↦
        A (fun i ↦ x i.castSucc)) : FunctionGerm (n + 1)) =
      functionGermPullbackHom (baseProjectionCLM n) (a : FunctionGerm n)
    rw [← hAa]
    rfl
  · rfl
  · intro y
    let c : Fin d → HolomorphicGerm n := fun i ↦ b.repr y i
    refine ⟨c, ?_, ?_⟩
    · rw [← b.sum_repr y]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hb]
      rfl
    · intro c' hc'
      funext i
      have hc'_basis : y = ∑ j, c' j • b j := by
        rw [hc']
        apply Finset.sum_congr rfl
        intro j hj
        rw [hb]
        rfl
      have hc_repr := congrArg (fun z ↦ b.repr z i) hc'_basis
      simp only [map_sum, map_smul, Module.Basis.repr_self,
        Finsupp.smul_single, smul_eq_mul, mul_one] at hc_repr
      simpa [c, Finsupp.single_apply] using hc_repr.symm

/-- Convert the implementation-oriented geometric predicate to its direct
coordinate formulation. -/
private theorem expandedGeometry_of_hasGeometricFiniteProjection
    {n d : ℕ} {F : ComplexEuclidean (n + 1) → ℂ}
    (h : HasGeometricFiniteProjection F d) :
    ∃ (a : Fin d → ComplexEuclidean n → ℂ)
        (u : ComplexEuclidean (n + 1) → ℂ)
        (U : Set (ComplexEuclidean n)) (R : ℝ),
      IsOpen U ∧ 0 ∈ U ∧ IsPreconnected U ∧ 0 < R ∧
      AnalyticOnNhd ℂ F
        {x | (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
          ‖x (Fin.last n)‖ < R} ∧
      (∀ i, AnalyticOnNhd ℂ (a i) U) ∧
      AnalyticOnNhd ℂ u
        {x | (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
          ‖x (Fin.last n)‖ < R} ∧
      (∀ i, a i 0 = 0) ∧
      (∀ x, (fun i : Fin n ↦ x i.castSucc) ∈ U →
        ‖x (Fin.last n)‖ < R →
        F x = u x *
          (x (Fin.last n) ^ d +
            ∑ i, a i (fun j : Fin n ↦ x j.castSucc) *
              x (Fin.last n) ^ (i : ℕ))) ∧
      (∀ x, (fun i : Fin n ↦ x i.castSucc) ∈ U →
        ‖x (Fin.last n)‖ < R → u x ≠ 0) ∧
      (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
        w ^ d + ∑ i, a i z * w ^ (i : ℕ) ≠ 0) ∧
      (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
        F (Fin.lastCases w z) ≠ 0) ∧
      (∀ z ∈ U, Set.Finite
        {w : ℂ | ‖w‖ < R ∧ F (Fin.lastCases w z) = 0}) ∧
      (∀ z ∈ U, Set.ncard
        {w : ℂ | ‖w‖ < R ∧ F (Fin.lastCases w z) = 0} ≤ d) ∧
      Function.Surjective
        (fun x :
            {x : ComplexEuclidean (n + 1) //
              (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
              ‖x (Fin.last n)‖ < R ∧ F x = 0} ↦
          (⟨(fun i : Fin n ↦ x.1 i.castSucc), x.2.1⟩ : U)) ∧
      IsProperMap
        (fun x :
            {x : ComplexEuclidean (n + 1) //
              (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
              ‖x (Fin.last n)‖ < R ∧ F x = 0} ↦
          (⟨(fun i : Fin n ↦ x.1 i.castSucc), x.2.1⟩ : U)) := by
  unfold HasGeometricFiniteProjection at h
  obtain ⟨a, u, U, R, hU, h0, hconn, hR, hF, ha, hu, ha0,
    hprepared, hunit, hpreparedBoundary, hFBoundary, hfinite,
    hncard, hsurj, hproper⟩ := h
  refine ⟨a, u, U, R, hU, h0, hconn, hR, ?_, ha, ?_, ha0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [dropLastCLM, baseProjectionCLM, lastCoordinateCLM,
      wptAmbientEquiv, wptAmbientLinearEquiv] using hF
  · simpa [dropLastCLM, baseProjectionCLM, lastCoordinateCLM,
      wptAmbientEquiv, wptAmbientLinearEquiv] using hu
  · simpa [dropLastCLM, baseProjectionCLM, lastCoordinateCLM,
      wptAmbientEquiv, wptAmbientLinearEquiv, preparedValue] using hprepared
  · simpa [dropLastCLM, baseProjectionCLM, lastCoordinateCLM,
      wptAmbientEquiv, wptAmbientLinearEquiv] using hunit
  · simpa [preparedValue] using hpreparedBoundary
  · simpa [appendLastCLE, wptAmbientEquiv, wptAmbientLinearEquiv] using
      hFBoundary
  · simpa [appendLastCLE, wptAmbientEquiv, wptAmbientLinearEquiv] using
      hfinite
  · simpa [appendLastCLE, wptAmbientEquiv, wptAmbientLinearEquiv] using
      hncard
  · change Function.Surjective (localProjection F U R)
    exact hsurj
  · change IsProperMap (localProjection F U R)
    exact hproper

/-- **Finite projection for a nontrivial analytic hypersurface germ.**

After a linear coordinate change, the transformed quotient has a unique
power expansion in the last coordinate.  The same representative has a
proper, surjective local projection with finite fibers and the full prepared
equation and boundary control.
-/
private theorem hypersurface_finiteProjection_expanded
    {n : ℕ} {f : HolomorphicGerm (n + 1)}
    (hf_ne : f ≠ 0)
    (hf_zero : Filter.Germ.value (f : FunctionGerm (n + 1)) = 0) :
    ∃ (L : ComplexEuclidean (n + 1) ≃L[ℂ]
          ComplexEuclidean (n + 1))
      (d : ℕ)
      (H F : ComplexEuclidean (n + 1) → ℂ)
      (g : HolomorphicGerm (n + 1)),
      0 < d ∧
      AnalyticAt ℂ H 0 ∧
      (H : FunctionGerm (n + 1)) = (f : FunctionGerm (n + 1)) ∧
      AnalyticAt ℂ F 0 ∧
      (F : FunctionGerm (n + 1)) =
        ((H ∘ L : ComplexEuclidean (n + 1) → ℂ) :
          FunctionGerm (n + 1)) ∧
      (g : FunctionGerm (n + 1)) = (F : FunctionGerm (n + 1)) ∧
      let I : Ideal (HolomorphicGerm (n + 1)) :=
        Ideal.span ({g} : Set (HolomorphicGerm (n + 1)))
      letI : I.IsTwoSided := Ideal.instIsTwoSided_1 I
      let q := Ideal.Quotient.mk I
      (∃ (ι : HolomorphicGerm n →+* HolomorphicGerm (n + 1))
          (w : HolomorphicGerm (n + 1)),
          (∀ (a : HolomorphicGerm n) (A : ComplexEuclidean n → ℂ),
            AnalyticAt ℂ A 0 →
            (A : FunctionGerm n) = (a : FunctionGerm n) →
            ((fun x : ComplexEuclidean (n + 1) ↦
                A (fun i ↦ x i.castSucc)) : FunctionGerm (n + 1)) =
              (ι a : FunctionGerm (n + 1))) ∧
          (((fun x : ComplexEuclidean (n + 1) ↦ x (Fin.last n)) :
              ComplexEuclidean (n + 1) → ℂ) : FunctionGerm (n + 1)) =
            (w : FunctionGerm (n + 1)) ∧
          ∀ y : HolomorphicGerm (n + 1) ⧸ I,
            ∃! c : Fin d → HolomorphicGerm n,
              (y = ∑ i, q (ι (c i) * w ^ (i : ℕ))))
      ∧
      ∃ (a : Fin d → ComplexEuclidean n → ℂ)
          (u : ComplexEuclidean (n + 1) → ℂ)
          (U : Set (ComplexEuclidean n)) (R : ℝ),
        IsOpen U ∧ 0 ∈ U ∧ IsPreconnected U ∧ 0 < R ∧
        AnalyticOnNhd ℂ F
          {x | (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
            ‖x (Fin.last n)‖ < R} ∧
        (∀ i, AnalyticOnNhd ℂ (a i) U) ∧
        AnalyticOnNhd ℂ u
          {x | (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
            ‖x (Fin.last n)‖ < R} ∧
        (∀ i, a i 0 = 0) ∧
        (∀ x, (fun i : Fin n ↦ x i.castSucc) ∈ U →
          ‖x (Fin.last n)‖ < R →
          F x = u x *
            (x (Fin.last n) ^ d +
              ∑ i, a i (fun j : Fin n ↦ x j.castSucc) *
                x (Fin.last n) ^ (i : ℕ))) ∧
        (∀ x, (fun i : Fin n ↦ x i.castSucc) ∈ U →
          ‖x (Fin.last n)‖ < R → u x ≠ 0) ∧
        (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
          w ^ d + ∑ i, a i z * w ^ (i : ℕ) ≠ 0) ∧
        (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
          F (Fin.lastCases w z) ≠ 0) ∧
        (∀ z ∈ U, Set.Finite
          {w : ℂ | ‖w‖ < R ∧ F (Fin.lastCases w z) = 0}) ∧
        (∀ z ∈ U, Set.ncard
          {w : ℂ | ‖w‖ < R ∧ F (Fin.lastCases w z) = 0} ≤ d) ∧
        Function.Surjective
          (fun x :
              {x : ComplexEuclidean (n + 1) //
                (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
                ‖x (Fin.last n)‖ < R ∧ F x = 0} ↦
            (⟨(fun i : Fin n ↦ x.1 i.castSucc), x.2.1⟩ : U)) ∧
        IsProperMap
          (fun x :
              {x : ComplexEuclidean (n + 1) //
                (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
                ‖x (Fin.last n)‖ < R ∧ F x = 0} ↦
            (⟨(fun i : Fin n ↦ x.1 i.castSucc), x.2.1⟩ : U)) := by
  obtain ⟨L, d, hd, hfinite, F, hF, hFcoord, hgeom⟩ :=
    hypersurface_finiteProjection_core hf_ne hf_zero
  obtain ⟨H, hH, hHrep⟩ := f.property
  let g : HolomorphicGerm (n + 1) := coordinatePullback L f
  have htransformed :
      (F : FunctionGerm (n + 1)) =
        ((H ∘ L : ComplexEuclidean (n + 1) → ℂ) :
          FunctionGerm (n + 1)) := by
    calc
      (F : FunctionGerm (n + 1)) =
          (coordinatePullback L f : FunctionGerm (n + 1)) := hFcoord
      _ = functionGermPullbackHom
          (L : ComplexEuclidean (n + 1) →L[ℂ]
            ComplexEuclidean (n + 1))
          (f : FunctionGerm (n + 1)) := rfl
      _ = functionGermPullbackHom
          (L : ComplexEuclidean (n + 1) →L[ℂ]
            ComplexEuclidean (n + 1))
          (H : FunctionGerm (n + 1)) := by rw [hHrep]
      _ = ((H ∘ L : ComplexEuclidean (n + 1) → ℂ) :
          FunctionGerm (n + 1)) := rfl
  have hpower : HasUniquePowerExpansion g d :=
    hasUniquePowerExpansion_of_isFiniteFreeOfRankOverBase hfinite
  have hgeom' := expandedGeometry_of_hasGeometricFiniteProjection hgeom
  refine ⟨L, d, H, F, g, hd, hH, hHrep, hF, htransformed,
    hFcoord.symm, ?_, hgeom'⟩
  simpa only [HasUniquePowerExpansion] using hpower

/-- **Finite projection for a nontrivial analytic hypersurface germ.**

This compared wrapper defines the analytic-germ rings locally, so its type is
Mathlib-only.  It is definitionally the expanded implementation theorem above.
-/
theorem hypersurface_finiteProjection :
    let E (k : ℕ) := Fin k → ℂ
    let G (k : ℕ) := Filter.Germ (nhds (0 : E k)) ℂ
    let O (k : ℕ) : Subring (G k) :=
      { carrier := {phi | ∃ f : E k → ℂ,
          AnalyticAt ℂ f 0 ∧ (f : G k) = phi}
        zero_mem' := ⟨0, analyticAt_const, rfl⟩
        one_mem' := ⟨1, analyticAt_const, rfl⟩
        add_mem' := by
          rintro phi psi ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
          exact ⟨f + g, hf.add hg, by simp⟩
        mul_mem' := by
          rintro phi psi ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
          exact ⟨f * g, hf.mul hg, by simp⟩
        neg_mem' := by
          rintro phi ⟨f, hf, rfl⟩
          exact ⟨-f, hf.neg, by simp⟩ }
    ∀ {n : ℕ} {f : O (n + 1)},
      f ≠ 0 →
      Filter.Germ.value (f : G (n + 1)) = 0 →
      ∃ (L : E (n + 1) ≃L[ℂ] E (n + 1))
        (d : ℕ)
        (H F : E (n + 1) → ℂ)
        (g : O (n + 1)),
        0 < d ∧
        AnalyticAt ℂ H 0 ∧
        (H : G (n + 1)) = (f : G (n + 1)) ∧
        AnalyticAt ℂ F 0 ∧
        (F : G (n + 1)) =
          ((H ∘ L : E (n + 1) → ℂ) : G (n + 1)) ∧
        (g : G (n + 1)) = (F : G (n + 1)) ∧
        let I : Ideal (O (n + 1)) :=
          Ideal.span ({g} : Set (O (n + 1)))
        letI : I.IsTwoSided := Ideal.instIsTwoSided_1 I
        let q := Ideal.Quotient.mk I
        (∃ (ι : O n →+* O (n + 1)) (w : O (n + 1)),
            (∀ (a : O n) (A : E n → ℂ),
              AnalyticAt ℂ A 0 →
              (A : G n) = (a : G n) →
              ((fun x : E (n + 1) ↦
                  A (fun i ↦ x i.castSucc)) : G (n + 1)) =
                (ι a : G (n + 1))) ∧
            (((fun x : E (n + 1) ↦ x (Fin.last n)) :
                E (n + 1) → ℂ) : G (n + 1)) =
              (w : G (n + 1)) ∧
            ∀ y : O (n + 1) ⧸ I,
              ∃! c : Fin d → O n,
                y = ∑ i, q (ι (c i) * w ^ (i : ℕ)))
        ∧
        ∃ (a : Fin d → E n → ℂ)
            (u : E (n + 1) → ℂ)
            (U : Set (E n)) (R : ℝ),
          IsOpen U ∧ 0 ∈ U ∧ IsPreconnected U ∧ 0 < R ∧
          AnalyticOnNhd ℂ F
            {x | (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
              ‖x (Fin.last n)‖ < R} ∧
          (∀ i, AnalyticOnNhd ℂ (a i) U) ∧
          AnalyticOnNhd ℂ u
            {x | (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
              ‖x (Fin.last n)‖ < R} ∧
          (∀ i, a i 0 = 0) ∧
          (∀ x, (fun i : Fin n ↦ x i.castSucc) ∈ U →
            ‖x (Fin.last n)‖ < R →
            F x = u x *
              (x (Fin.last n) ^ d +
                ∑ i, a i (fun j : Fin n ↦ x j.castSucc) *
                  x (Fin.last n) ^ (i : ℕ))) ∧
          (∀ x, (fun i : Fin n ↦ x i.castSucc) ∈ U →
            ‖x (Fin.last n)‖ < R → u x ≠ 0) ∧
          (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
            w ^ d + ∑ i, a i z * w ^ (i : ℕ) ≠ 0) ∧
          (∀ z ∈ U, ∀ w : ℂ, ‖w‖ = R →
            F (Fin.lastCases w z) ≠ 0) ∧
          (∀ z ∈ U, Set.Finite
            {w : ℂ | ‖w‖ < R ∧ F (Fin.lastCases w z) = 0}) ∧
          (∀ z ∈ U, Set.ncard
            {w : ℂ | ‖w‖ < R ∧ F (Fin.lastCases w z) = 0} ≤ d) ∧
          Function.Surjective
            (fun x :
                {x : E (n + 1) //
                  (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
                  ‖x (Fin.last n)‖ < R ∧ F x = 0} ↦
              (⟨(fun i : Fin n ↦ x.1 i.castSucc), x.2.1⟩ : U)) ∧
          IsProperMap
            (fun x :
                {x : E (n + 1) //
                  (fun i : Fin n ↦ x i.castSucc) ∈ U ∧
                  ‖x (Fin.last n)‖ < R ∧ F x = 0} ↦
              (⟨(fun i : Fin n ↦ x.1 i.castSucc), x.2.1⟩ : U)) := by
  dsimp only
  intro n f hf_ne hf_zero
  exact hypersurface_finiteProjection_expanded hf_ne hf_zero

attribute [-instance] RCLike.innerProductSpace in
/-- The holomorphic constant-rank normal form in direct coordinates. -/
theorem holomorphic_constantRank_normalForm
    {n m r : ℕ}
    {F : (Fin n → ℂ) → (Fin m → ℂ)}
    {a : Fin n → ℂ}
    (hF : AnalyticAt ℂ F a)
    (hrn : r ≤ n)
    (hrm : r ≤ m)
    (hconst : ∀ᶠ x in nhds a,
      Module.finrank ℂ
        (LinearMap.range (fderiv ℂ F x).toLinearMap) = r) :
    ∃ (sourceCoord sourceInv : (Fin n → ℂ) → (Fin n → ℂ))
      (targetCoord targetInv : (Fin m → ℂ) → (Fin m → ℂ)),
      sourceCoord a = 0 ∧
      sourceInv 0 = a ∧
      targetCoord (F a) = 0 ∧
      targetInv 0 = F a ∧
      AnalyticAt ℂ sourceCoord a ∧
      AnalyticAt ℂ sourceInv 0 ∧
      AnalyticAt ℂ targetCoord (F a) ∧
      AnalyticAt ℂ targetInv 0 ∧
      (fun x ↦ sourceInv (sourceCoord x)) =ᶠ[nhds a] (fun x ↦ x) ∧
      (fun x ↦ sourceCoord (sourceInv x)) =ᶠ[nhds 0] (fun x ↦ x) ∧
      (fun y ↦ targetInv (targetCoord y)) =ᶠ[nhds (F a)] (fun y ↦ y) ∧
      (fun y ↦ targetCoord (targetInv y)) =ᶠ[nhds 0] (fun y ↦ y) ∧
      (fun x ↦ targetCoord (F (sourceInv x))) =ᶠ[nhds 0]
        (fun x j ↦
          if h : j.1 < r then
            x ⟨j.1, lt_of_lt_of_le h hrn⟩
          else 0) := by
  have hconst' : ∀ᶠ x in nhds a,
      complexRank (fderiv ℂ F x) = r := by
    simpa only [complexRank] using hconst
  obtain ⟨phi, psi, hnormal⟩ :=
    holomorphic_constantRank_normalForm_core hF hrn hrm hconst'
  refine ⟨phi.toFun, phi.invFun, psi.toFun, psi.invFun,
    phi.map_source, phi.map_target, psi.map_source, psi.map_target,
    phi.analyticAt_toFun, phi.analyticAt_invFun,
    psi.analyticAt_toFun, psi.analyticAt_invFun,
    phi.left_inv, phi.right_inv, psi.left_inv, psi.right_inv, ?_⟩
  refine hnormal.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  funext j
  rw [standardRankMap_apply]
  by_cases hjr : j.1 < r
  · have hjn : j.1 < n := lt_of_lt_of_le hjr hrn
    simp only [hjr, hjn, and_self, dite_true]
  · simp only [hjr, and_false, dite_false]

/-- **Ruckert's local analytic Nullstellensatz.** -/
theorem localAnalyticNullstellensatz
    {n s : ℕ}
    {f : Fin s → (Fin n → ℂ) → ℂ}
    {g : (Fin n → ℂ) → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) 0)
    (hg : AnalyticAt ℂ g 0)
    (hzero : ∀ᶠ x in nhds (0 : Fin n → ℂ),
      (∀ i, f i x = 0) → g x = 0) :
    ∃ N : ℕ, 0 < N ∧
      ∃ h : Fin s → (Fin n → ℂ) → ℂ,
        (∀ i, AnalyticAt ℂ (h i) 0) ∧
        (fun x ↦ g x ^ N) =ᶠ[nhds 0]
          fun x ↦ ∑ i, h i x * f i x :=
  localAnalyticNullstellensatz_core hf hg hzero

end

end LocalComplexGeometry
