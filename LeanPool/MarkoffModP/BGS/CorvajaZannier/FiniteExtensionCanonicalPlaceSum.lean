/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.GlobalWronskianWeightedPlaceSum
import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionCanonicalWronskian
import Mathlib.Tactic

open scoped BigOperators

namespace BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

attribute [local instance] Classical.decEq

/-- The finite set on which all terms in the canonical Wronskian summation
can be nonzero. -/
def finiteExtensionCanonicalSummationSupport
    (S : Finset (FiniteExtensionPlace K L))
    (canonical : FiniteExtensionPlace K L →₀ ℤ)
    (u v rho grid W : L) : Finset (FiniteExtensionPlace K L) := by
  classical
  exact S ∪ canonical.support ∪
    (finiteExtensionPrincipalDivisor K L u).support ∪
    (finiteExtensionPrincipalDivisor K L v).support ∪
    (finiteExtensionPrincipalDivisor K L rho).support ∪
    (finiteExtensionPrincipalDivisor K L grid).support ∪
    (finiteExtensionPrincipalDivisor K L W).support

/-- The pole height of `rho` away from an exceptional set. -/
def finiteExtensionOutsideHeight
    (rho : L) (S : Finset (FiniteExtensionPlace K L)) : ℕ := by
  classical
  exact ∑ P ∈ (finiteExtensionPrincipalDivisor K L rho).support.filter
      (fun P => P ∉ S ∧ finiteExtensionPrincipalDivisor K L rho P < 0),
    (finiteExtensionPrincipalDivisor K L rho P).natAbs *
      finiteExtensionPlaceDegree K L P

theorem finiteExtensionOutsideHeight_negativeSum
    (rho : L) (S : Finset (FiniteExtensionPlace K L)) :
    ∑ P ∈ (finiteExtensionPrincipalDivisor K L rho).support.filter
        (fun P => P ∉ S ∧ finiteExtensionPrincipalDivisor K L rho P < 0),
      finiteExtensionPrincipalDivisor K L rho P *
        (finiteExtensionPlaceDegree K L P : ℤ) =
      -(finiteExtensionOutsideHeight K L rho S : ℤ) := by
  classical
  rw [finiteExtensionOutsideHeight, Nat.cast_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro P hP
  have hneg : finiteExtensionPrincipalDivisor K L rho P < 0 :=
    (Finset.mem_filter.mp hP).2.2
  rw [Nat.cast_mul, Int.natCast_natAbs, abs_of_nonpos (le_of_lt hneg)]
  ring

/-- Exhaustive residue-degree-weighted summation with a genuine canonical
divisor and a nonzero global Wronskian. -/
theorem globalWronskianInequality_of_finiteExtensionCanonicalPlacewiseBounds
    (S : Finset (FiniteExtensionPlace K L))
    (canonical : FiniteExtensionPlace K L →₀ ℤ)
    (u v rho grid W : L)
    (h k n sigma chi : ℕ)
    (hu : u ≠ 0) (hgrid : grid ≠ 0) (hW : W ≠ 0)
    (hUOutside : ∀ P, P ∉ S → finiteExtensionPrincipalDivisor K L u P = 0)
    (hGridOutside : ∀ P, P ∉ S →
      finiteExtensionPrincipalDivisor K L grid P = 0)
    (hVPositiveSupport : ∀ P,
      0 < finiteExtensionPrincipalDivisor K L v P → P ∈ S)
    (hEuler : finiteExtensionDivisorDegree K L canonical +
      (∑ P ∈ S, finiteExtensionPlaceDegree K L P : ℤ) ≤ (chi : ℤ))
    (hRhoSupport :
      -((finiteExtensionPositiveDegree K L u : ℤ) +
          (finiteExtensionPositiveDegree K L v : ℤ)) ≤
        ∑ P ∈ S, finiteExtensionPrincipalDivisor K L rho P *
          (finiteExtensionPlaceDegree K L P : ℤ))
    (hCaseI : ∀ P, P ∉ S →
      finiteExtensionPrincipalDivisor K L rho P < 0 →
      (n : ℤ) * finiteExtensionPrincipalDivisor K L rho P ≤
        (sigma : ℤ) * canonical P +
          finiteExtensionPrincipalDivisor K L W P)
    (hCaseII : ∀ P, P ∉ S →
      0 ≤ finiteExtensionPrincipalDivisor K L rho P →
      0 ≤ (sigma : ℤ) * canonical P +
        finiteExtensionPrincipalDivisor K L W P)
    (hCaseIII : ∀ P, P ∈ S →
      0 < finiteExtensionPrincipalDivisor K L v P →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L u P +
        ((h * k : ℕ) : ℤ) * finiteExtensionPrincipalDivisor K L v P +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L rho P +
        finiteExtensionPrincipalDivisor K L grid P - (sigma : ℤ) ≤
          (sigma : ℤ) * canonical P +
            finiteExtensionPrincipalDivisor K L W P)
    (hCaseIV : ∀ P, P ∈ S →
      finiteExtensionPrincipalDivisor K L v P ≤ 0 →
      ((k * (k - 1) / 2 : ℕ) : ℤ) *
          finiteExtensionPrincipalDivisor K L u P +
        (k : ℤ) * finiteExtensionPrincipalDivisor K L rho P +
        finiteExtensionPrincipalDivisor K L grid P - (sigma : ℤ) ≤
          (sigma : ℤ) * canonical P +
            finiteExtensionPrincipalDivisor K L W P) :
    ((h * k : ℕ) : ℤ) * (finiteExtensionPositiveDegree K L v : ℤ) -
        (k : ℤ) * ((finiteExtensionPositiveDegree K L u : ℤ) +
          (finiteExtensionPositiveDegree K L v : ℤ)) -
        (sigma : ℤ) * (chi : ℤ) ≤
      (n : ℤ) * (finiteExtensionOutsideHeight K L rho S : ℤ) := by
  classical
  let T := finiteExtensionCanonicalSummationSupport K L S canonical u v rho grid W
  let I := {P // P ∈ T}
  let eS : {P // P ∈ S} ↪ I :=
    ⟨fun P => ⟨P.1, by
        change P.1 ∈ finiteExtensionCanonicalSummationSupport K L S canonical u v rho grid W
        simp [finiteExtensionCanonicalSummationSupport, P.2]⟩,
      fun P Q hPQ => Subtype.ext
        (congrArg (fun R : I => R.1) hPQ)⟩
  let S' : Finset I := S.attach.map eS
  let ord (x : L) : I → ℤ := fun P => finiteExtensionPrincipalDivisor K L x P.1
  let ordW : I → ℤ := fun P =>
    (sigma : ℤ) * canonical P.1 + finiteExtensionPrincipalDivisor K L W P.1
  have hS'_iff (P : I) : P ∈ S' ↔ P.1 ∈ S := by
    constructor
    · intro hP
      rcases Finset.mem_map.mp hP with ⟨Q, hQS, hQP⟩
      have : Q.1 = P.1 := congrArg Subtype.val hQP
      simpa [this] using Q.2
    · intro hP
      let Q : {P // P ∈ S} := ⟨P.1, hP⟩
      have hQattach : Q ∈ S.attach := by simp [Q]
      apply Finset.mem_map.mpr
      refine ⟨Q, hQattach, ?_⟩
      apply Subtype.ext
      rfl
  have hsum_of_support_subset
      (D : FiniteExtensionPlace K L →₀ ℤ) (hDT : D.support ⊆ T) :
      ∑ P : I, D P.1 * (finiteExtensionPlaceDegree K L P.1 : ℤ) =
        D.sum (fun P a => a * (finiteExtensionPlaceDegree K L P : ℤ)) := by
    rw [← Finset.sum_subtype T (fun P => by simp) (fun P =>
      D P * (finiteExtensionPlaceDegree K L P : ℤ))]
    symm
    exact Finsupp.sum_of_support_subset D hDT
      (fun P a => a * (finiteExtensionPlaceDegree K L P : ℤ))
      (by simp)
  have hcanonicalSupport : canonical.support ⊆ T := by
    intro P hP
    simp [T, finiteExtensionCanonicalSummationSupport, hP]
  have hWsupport : (finiteExtensionPrincipalDivisor K L W).support ⊆ T := by
    intro P hP
    simp [T, finiteExtensionCanonicalSummationSupport, hP]
  have hUSum : ∑ P : I, ord u P *
      (finiteExtensionPlaceDegree K L P.1 : ℤ) = 0 := by
    rw [hsum_of_support_subset (finiteExtensionPrincipalDivisor K L u)]
    · exact finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L u hu
    · intro P hP
      simp [T, finiteExtensionCanonicalSummationSupport, hP]
  have hGridSum : ∑ P : I, ord grid P *
      (finiteExtensionPlaceDegree K L P.1 : ℤ) = 0 := by
    rw [hsum_of_support_subset (finiteExtensionPrincipalDivisor K L grid)]
    · exact finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L grid hgrid
    · intro P hP
      simp [T, finiteExtensionCanonicalSummationSupport, hP]
  have hCanonicalSum : ∑ P : I, ordW P *
      (finiteExtensionPlaceDegree K L P.1 : ℤ) =
      (sigma : ℤ) * finiteExtensionDivisorDegree K L canonical := by
    change ∑ P : I,
        ((sigma : ℤ) * canonical P.1 +
          finiteExtensionPrincipalDivisor K L W P.1) *
          (finiteExtensionPlaceDegree K L P.1 : ℤ) = _
    simp_rw [add_mul, Finset.sum_add_distrib]
    have hscale :
        (∑ P : I, (sigma : ℤ) * canonical P.1 *
          (finiteExtensionPlaceDegree K L P.1 : ℤ)) =
        (sigma : ℤ) * ∑ P : I, canonical P.1 *
          (finiteExtensionPlaceDegree K L P.1 : ℤ) := by
      calc
        _ = ∑ P : I, (sigma : ℤ) *
            (canonical P.1 * (finiteExtensionPlaceDegree K L P.1 : ℤ)) := by
              apply Finset.sum_congr rfl
              intro P hP
              ring
        _ = _ := by rw [Finset.mul_sum]
    rw [hscale]
    rw [hsum_of_support_subset canonical hcanonicalSupport,
      hsum_of_support_subset (finiteExtensionPrincipalDivisor K L W) hWsupport]
    have hprincipal := finiteExtensionPrincipalDivisorDegreeSum_eq_zero K L W hW
    change (finiteExtensionPrincipalDivisor K L W).sum
      (fun P a => a * (finiteExtensionPlaceDegree K L P : ℤ)) = 0 at hprincipal
    rw [hprincipal, add_zero]
    rfl
  have hDegreeS : ∑ P ∈ S', finiteExtensionPlaceDegree K L P.1 =
      ∑ P ∈ S, finiteExtensionPlaceDegree K L P := by
    change ∑ P ∈ S.attach.map eS, finiteExtensionPlaceDegree K L P.1 = _
    rw [Finset.sum_map]
    change ∑ P ∈ S.attach, finiteExtensionPlaceDegree K L P.1 = _
    exact Finset.sum_attach S (fun P => finiteExtensionPlaceDegree K L P)
  have hSumS (F : FiniteExtensionPlace K L → ℤ) :
      ∑ P ∈ S', F P.1 = ∑ P ∈ S, F P := by
    change ∑ P ∈ S.attach.map eS, F P.1 = _
    rw [Finset.sum_map]
    change ∑ P ∈ S.attach, F P.1 = _
    exact Finset.sum_attach S F
  have hOutside :
      ∑ P ∈ Finset.univ.filter (fun P : I => P ∉ S' ∧ ord rho P < 0),
        ord rho P * (finiteExtensionPlaceDegree K L P.1 : ℤ) =
      -(finiteExtensionOutsideHeight K L rho S : ℤ) := by
    let R := (finiteExtensionPrincipalDivisor K L rho).support.filter
      (fun P => P ∉ S ∧ finiteExtensionPrincipalDivisor K L rho P < 0)
    have hRT : R ⊆ T := by
      intro P hP
      have hsupport : P ∈ (finiteExtensionPrincipalDivisor K L rho).support :=
        (Finset.mem_filter.mp hP).1
      simp [T, finiteExtensionCanonicalSummationSupport, hsupport]
    let eR : {P // P ∈ R} ↪ I :=
      ⟨fun P => ⟨P.1, hRT P.2⟩,
        fun P Q hPQ => Subtype.ext
          (congrArg (fun R : I => R.1) hPQ)⟩
    have hfilter : Finset.univ.filter (fun P : I => P ∉ S' ∧ ord rho P < 0) =
        R.attach.map eR := by
      ext P
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        ]
      constructor
      · intro hP
        have hne : finiteExtensionPrincipalDivisor K L rho P.1 ≠ 0 :=
          ne_of_lt hP.2
        have hmemR : P.1 ∈ R := by
          apply Finset.mem_filter.mpr
          refine ⟨Finsupp.mem_support_iff.mpr hne, ?_, hP.2⟩
          intro hPS
          exact hP.1 ((hS'_iff P).mpr hPS)
        let Q : {P // P ∈ R} := ⟨P.1, hmemR⟩
        refine ⟨Q, by simp, ?_⟩
        apply Subtype.ext
        rfl
      · rintro ⟨Q, hQattach, hQP⟩
        have hval : Q.1 = P.1 := congrArg (fun R : I => R.1) hQP
        have hQR := (Finset.mem_filter.mp Q.2).2
        constructor
        · rw [hS'_iff]
          simpa [hval] using hQR.1
        · simpa [ord, hval] using hQR.2
    rw [hfilter, Finset.sum_map]
    change ∑ Q ∈ R.attach,
        finiteExtensionPrincipalDivisor K L rho Q.1 *
          (finiteExtensionPlaceDegree K L Q.1 : ℤ) = _
    calc
      _ = ∑ P ∈ R, finiteExtensionPrincipalDivisor K L rho P *
          (finiteExtensionPlaceDegree K L P : ℤ) :=
        Finset.sum_attach R (fun P => finiteExtensionPrincipalDivisor K L rho P *
          (finiteExtensionPlaceDegree K L P : ℤ))
      _ = _ := by
        simpa [R] using finiteExtensionOutsideHeight_negativeSum K L rho S
  apply globalWronskianInequality_of_weightedPlacewiseBounds
    (fun P : I => finiteExtensionPlaceDegree K L P.1) S'
    (ord u) (ord v) (ord rho) (ord grid) ordW
    h k n sigma
    (finiteExtensionPositiveDegree K L u)
    (finiteExtensionPositiveDegree K L v)
    chi (finiteExtensionOutsideHeight K L rho S)
    (finiteExtensionDivisorDegree K L canonical)
  · intro P hP
    exact hUOutside P.1 ((hS'_iff P).not.mp hP)
  · intro P hP
    exact hGridOutside P.1 ((hS'_iff P).not.mp hP)
  · exact hUSum
  · exact hGridSum
  · have hpositive : ∀ P : I, 0 < ord v P → P ∈ S' := by
      intro P hP
      rw [hS'_iff]
      exact hVPositiveSupport P.1 hP
    let D := finiteExtensionPrincipalDivisor K L v
    have hDsupport : D.support ⊆ T := by
      intro P hP
      have hne : finiteExtensionPrincipalDivisor K L v P ≠ 0 := by
        simpa [D, Finsupp.mem_support_iff] using
          (Finsupp.mem_support_iff.mp hP)
      simp [T, finiteExtensionCanonicalSummationSupport,
        Finsupp.mem_support_iff, hne]
    have hPositiveAll :
        (∑ P : I, if 0 < ord v P then
          ord v P * (finiteExtensionPlaceDegree K L P.1 : ℤ) else 0) =
        (finiteExtensionPositiveDegree K L v : ℤ) := by
      calc
        _ = ∑ P ∈ T, if 0 < D P then
            D P * (finiteExtensionPlaceDegree K L P : ℤ) else 0 := by
              exact (Finset.sum_subtype T (fun P => by simp)
                (fun P => if 0 < D P then
                  D P * (finiteExtensionPlaceDegree K L P : ℤ) else 0)).symm
        _ = ∑ P ∈ D.support, if 0 < D P then
            D P * (finiteExtensionPlaceDegree K L P : ℤ) else 0 := by
              apply Eq.symm
              apply Finset.sum_subset hDsupport
              intro P hPT hnot
              have hzero : D P = 0 := Finsupp.notMem_support_iff.mp hnot
              simp [hzero]
        _ = ∑ P ∈ D.support.filter (fun P => 0 < D P),
            D P * (finiteExtensionPlaceDegree K L P : ℤ) := by
              rw [Finset.sum_filter]
        _ = (finiteExtensionPositiveDegree K L v : ℤ) := by
              exact (finiteExtensionPositiveDegree_cast K L v).symm
    calc
      ∑ P ∈ S'.filter (fun P => 0 < ord v P),
          ord v P * (finiteExtensionPlaceDegree K L P.1 : ℤ) =
          ∑ P ∈ S', if 0 < ord v P then
            ord v P * (finiteExtensionPlaceDegree K L P.1 : ℤ) else 0 := by
              rw [Finset.sum_filter]
      _ = ∑ P : I, if 0 < ord v P then
            ord v P * (finiteExtensionPlaceDegree K L P.1 : ℤ) else 0 := by
              apply Finset.sum_subset (Finset.subset_univ S')
              intro P hP hnotS
              have hnotpos : ¬ 0 < ord v P := by
                intro hpos
                exact hnotS (hpositive P hpos)
              simp [hnotpos]
      _ = _ := hPositiveAll
  · exact hOutside
  · exact hCanonicalSum
  · rw [hDegreeS]
    simpa only [Nat.cast_sum] using hEuler
  · change -((finiteExtensionPositiveDegree K L u : ℤ) +
        (finiteExtensionPositiveDegree K L v : ℤ)) ≤
      ∑ P ∈ S', finiteExtensionPrincipalDivisor K L rho P.1 *
        (finiteExtensionPlaceDegree K L P.1 : ℤ)
    rw [hSumS (fun P => finiteExtensionPrincipalDivisor K L rho P *
      (finiteExtensionPlaceDegree K L P : ℤ))]
    exact hRhoSupport
  · intro P hPS hneg
    exact hCaseI P.1 ((hS'_iff P).not.mp hPS) hneg
  · intro P hPS hnonneg
    exact hCaseII P.1 ((hS'_iff P).not.mp hPS) hnonneg
  · intro P hPS hpos
    exact hCaseIII P.1 ((hS'_iff P).mp hPS) hpos
  · intro P hPS hnonpos
    exact hCaseIV P.1 ((hS'_iff P).mp hPS) hnonpos

end

end BGS.CorvajaZannier
