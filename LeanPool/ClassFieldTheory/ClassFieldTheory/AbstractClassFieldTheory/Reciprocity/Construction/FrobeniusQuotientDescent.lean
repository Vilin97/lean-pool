/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent

/-! # Frobenius Quotient Descent -/

@[expose] public section
universe u v

namespace ClassFormation

open KummerTheory
open CyclicCohomology

/-!
# Frobenius quotient descent

This module constructs the Frobenius quotient representation, identifies its
Birkhoff sums with Frobenius power sums, and proves the finite-support
descent from the maximal unramified field.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

section representationDescent

/-!
Mathlib's `Rep ℤ G` requires its coefficient ring and acting group in the
same universe; `IntegralRepGroupType` names that shared boundary.
-/
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Underlying coefficient of the actual quotient action, expressed through
the chosen quotient representative. -/
theorem frobeniusQuotientAction_coe_out (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    (D.frobeniusQuotientAction A K L hLK q a).1 =
      A.ρ (Quotient.out q).1 a.1 := by
  let k : K.toSubgroup := Quotient.out q
  have hkq : (QuotientGroup.mk k :
      K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) = q :=
    Quotient.out_eq' q
  calc
    (D.frobeniusQuotientAction A K L hLK q a).1 =
        (D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a).1 :=
      congrArg (fun z => (D.frobeniusQuotientAction A K L hLK z a).1) hkq.symm
    _ = A.ρ k.1 a.1 := rfl
    _ = A.ρ (Quotient.out q).1 a.1 := rfl

/-- The linear action of `G(\widetilde L/K)` on
`A_{\widetilde L}`.  This packages the concrete quotient action from
the Frobenius norm-identity lemma in the form needed by the Tate-cohomology calculation. -/
noncomputable def frobeniusQuotientActionLinearMap (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) →ₗ[ℤ]
      ambientFixedAddSubgroup A (D.maximalUnramifiedField L) where
  toFun := D.frobeniusQuotientAction A K L hLK q
  map_add' a b := by
    refine Quotient.inductionOn' q ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 (a.1 + b.1) = A.ρ k.1 a.1 + A.ρ k.1 b.1
    exact map_add (A.ρ k.1) _ _
  map_smul' n a := by
    refine Quotient.inductionOn' q ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 (n • a.1) = n • A.ρ k.1 a.1
    exact map_zsmul (A.ρ k.1) n a.1

/-- The actual `G(\widetilde L/K)`-representation on
`A_{\widetilde L}` used in the universal norm-descent lemma. -/
noncomputable def frobeniusQuotientRepresentation (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal] :
    Rep ℤ (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  Rep.of
    { toFun := D.frobeniusQuotientActionLinearMap A K L hLK
      map_one' := by
        ext a
        change A.ρ (1 : G) a.1 = a.1
        simp
      map_mul' := by
        intro q r
        refine Quotient.inductionOn₂' q r ?_
        intro k l
        ext a
        change A.ρ (k.1 * l.1) a.1 = A.ρ k.1 (A.ρ l.1 a.1)
        rw [map_mul]
        rfl }

/-- The Frobenius quotient representation evaluates by the chosen quotient action. -/
@[simp]
theorem frobeniusQuotientRepresentation_apply (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    (D.frobeniusQuotientRepresentation A K L hLK).ρ q a =
      D.frobeniusQuotientAction A K L hLK q a :=
  rfl

/-- The Birkhoff sum of the quotient action is the corresponding sum of Frobenius powers. -/
theorem birkhoffSum_eq_frobeniusPowerSum (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    birkhoffSum
        ((D.frobeniusQuotientRepresentation A K L hLK).ρ φ) id n a =
      D.frobeniusPowerSum A K L hLK φ n a := by
  unfold birkhoffSum frobeniusPowerSum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [id_eq, Finset.mem_range.mp hi, dite_true]
  exact (rep_action_pow_eq_iterate
    (D.frobeniusQuotientRepresentation A K L hLK) φ i a).symm

/-- A Frobenius power sum splits into its first `n` terms and a translated
block of `m` terms. -/
theorem frobeniusPowerSum_add (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n m : ℕ)
    (x : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusPowerSum A K L hLK φ (n + m) x =
      D.frobeniusPowerSum A K L hLK φ n x +
        D.frobeniusPowerSum A K L hLK φ m
          (D.frobeniusQuotientAction A K L hLK (φ ^ n) x) := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have hsum (r : ℕ)
      (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
      birkhoffSum (B.ρ φ) id r a =
        D.frobeniusPowerSum A K L hLK φ r a :=
    D.birkhoffSum_eq_frobeniusPowerSum A K L hLK φ r a
  have hiterate : ((B.ρ φ)^[n]) x =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) x :=
    (rep_action_pow_eq_iterate B φ n x).symm
  exact ((hsum (n + m) x).symm.trans
    (birkhoffSum_add_right_apply (B.ρ φ) id n m x)).trans
      (congrArg₂
        (fun a b : ambientFixedAddSubgroup A (D.maximalUnramifiedField L) => a + b)
        (hsum n x)
        ((hsum m (((B.ρ φ)^[n]) x)).trans
          (congrArg (D.frobeniusPowerSum A K L hLK φ m) hiterate)))

/-- Actual additive telescoping identity for the Frobenius power sum. -/
theorem frobeniusPowerSum_action_sub (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusQuotientAction A K L hLK φ
        (D.frobeniusPowerSum A K L hLK φ n a) -
        D.frobeniusPowerSum A K L hLK φ n a =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) a - a := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have h := birkhoffSum_apply_sub_birkhoffSum (B.ρ φ) id n a
  have hshift :
      B.ρ φ (birkhoffSum (B.ρ φ) id n a) =
        birkhoffSum (B.ρ φ) id n (B.ρ φ a) := by
    calc
      B.ρ φ (birkhoffSum (B.ρ φ) id n a) =
          birkhoffSum (B.ρ φ) (B.ρ φ ∘ id) n a :=
        map_birkhoffSum (B.ρ φ) (B.ρ φ) id n a
      _ = birkhoffSum (B.ρ φ) id n (B.ρ φ a) := by
        unfold birkhoffSum
        apply Finset.sum_congr rfl
        intro i _
        simp only [Function.comp_apply, id_eq]
        exact (Function.Commute.self_iterate (B.ρ φ) i).eq a
  rw [← hshift] at h
  simp only [id_eq] at h
  rw [D.birkhoffSum_eq_frobeniusPowerSum A K L hLK,
    ← rep_action_pow_eq_iterate B φ n a] at h
  change
    D.frobeniusQuotientAction A K L hLK φ
          (D.frobeniusPowerSum A K L hLK φ n a) -
        D.frobeniusPowerSum A K L hLK φ n a =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) a - a at h
  exact h

/-- The difference of Frobenius power sums is represented by universal norm descent. -/
theorem frobeniusPowerSum_sub_universalNormDescent (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (x y : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusPowerSum A K L hLK φ n (x - y) =
      D.frobeniusPowerSum A K L hLK φ n x -
        D.frobeniusPowerSum A K L hLK φ n y := by
  unfold DegreeData.frobeniusPowerSum
  change
    (∑ i : Fin n,
      D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) (x - y)) =
      (∑ i : Fin n,
        D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) x) -
      ∑ i : Fin n,
        D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) y
  simp only [map_sub, Finset.sum_sub_distrib]

/-- An orbit sum of an element fixed by its first translate is scalar
multiplication by the orbit length. -/
theorem frobeniusPowerSum_eq_nsmul_of_fixed (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : D.frobeniusQuotientAction A K L hLK q a = a) :
    D.frobeniusPowerSum A K L hLK q n a = n • a := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have hpow (i : ℕ) :
      D.frobeniusQuotientAction A K L hLK (q ^ i) a = a := by
    have haB : B.ρ q a = a := by
      change D.frobeniusQuotientAction A K L hLK q a = a
      exact ha
    have hi := rep_action_pow_fixed B q a haB i
    change D.frobeniusQuotientAction A K L hLK (q ^ i) a = a at hi
    exact hi
  unfold DegreeData.frobeniusPowerSum
  simp_rw [hpow]
  simp

/-- Equivariance of `N_{\widetilde L/\widetilde K}` expressed inside
`A_{\widetilde L}`. -/
theorem maximalUnramifiedNorm_frobeniusQuotientAction (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (extensionSubgroup K L hLK).Normal]
    [Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    letI : Finite
        ((D.maximalUnramifiedField K).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K L hLK
    fixedFieldInclusion A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (D.frobeniusQuotientAction A K L hLK q a)) =
      D.frobeniusQuotientAction A K L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
            a)) := by
  let : Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K L hLK
  apply Subtype.ext
  exact D.relativeNorm_frobeniusQuotientAction A K L hLK q a

/-- A degree-zero element acts trivially on an element already defined
over `\widetilde K`. -/
theorem frobeniusQuotientAction_fixed_of_degreeZero (D : DegreeData G)
    (A : Rep ℤ G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field)) :
    D.frobeniusQuotientAction A K.field L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a) =
      fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) a := by
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  have hkDegree : D.normalizedDegree K k = 1 := by
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) := rfl
      _ = D.extensionNormalizedDegree K L hLK q :=
        congrArg (D.extensionNormalizedDegree K L hLK) hkq
      _ = 1 := hq
  have hkInertia : k ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    exact hkDegree
  let kI : (D.maximalUnramifiedField K.field).toSubgroup :=
    ⟨k.1, ⟨k.2, hkInertia⟩⟩
  rw [← hkq]
  apply Subtype.ext
  exact a.2 kI

/-- Applying `N_{\widetilde L/\widetilde K}` to equation `(*)` kills
all degree-zero differences.  Hence the norm of `u` is fixed by the
chosen degree-one Frobenius element. -/
theorem maximalUnramifiedNorm_fixed_of_hstar (D : DegreeData G)
    (A : Rep ℤ G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker)
    (u : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (uᵢ : ι → ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ u - u =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i) - uᵢ i)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          extensionSubgroup (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)) :=
      D.maximalUnramifiedExtension_finite K.field L hLK
    let N := relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) (N u)
    D.frobeniusQuotientAction A K.field L hLK φ b = b := by
  dsimp only
  let : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        extensionSubgroup (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)) :=
    D.maximalUnramifiedExtension_finite K.field L hLK
  let N := relativeNorm A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  let J := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  have hnorm := congrArg (J.comp N) hstar
  simp only [map_sub, map_sum] at hnorm
  change J (N (D.frobeniusQuotientAction A K.field L hLK φ u)) - J (N u) =
    ∑ i ∈ s,
      (J (N (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i))) -
        J (N (uᵢ i))) at hnorm
  have hφEquiv :
      J (N (D.frobeniusQuotientAction A K.field L hLK φ u)) =
        D.frobeniusQuotientAction A K.field L hLK φ (J (N u)) := by
    simpa [J, N] using
      D.maximalUnramifiedNorm_frobeniusQuotientAction A K.field L hLK φ u
  rw [hφEquiv] at hnorm
  have hzero (i : ι) :
      J (N (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i))) =
        J (N (uᵢ i)) := by
    calc
      J (N (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i))) =
          D.frobeniusQuotientAction A K.field L hLK (τ i).1 (J (N (uᵢ i))) := by
        simpa [J, N] using
          D.maximalUnramifiedNorm_frobeniusQuotientAction
            A K.field L hLK (τ i).1 (uᵢ i)
      _ = J (N (uᵢ i)) := by
        simpa [J, N] using D.frobeniusQuotientAction_fixed_of_degreeZero
          A K L hLK (τ i).1 (τ i).2 (N (uᵢ i))
  simp_rw [hzero] at hnorm
  have hnormzero :
      D.frobeniusQuotientAction A K.field L hLK φ (J (N u)) - J (N u) = 0 := by
    simpa only [sub_self, Finset.sum_const_zero] using hnorm
  simpa [J, N] using sub_eq_zero.mp hnormzero

/-- A `\widetilde K`-fixed element with finite Galois support descends to
`K` as soon as it is fixed by a degree-one Frobenius lift.  The proof is
the finite-quotient argument implicit: the finite degree-quotient decomposition writes
each element of `Gal(P/K)` as a positive Frobenius power up to inertia. -/
theorem descend_maximalUnramified_fixed_of_finiteSupport (D : DegreeData G)
    (A : Rep ℤ G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (extensionSubgroup K.field P.field P.below).Normal]
    (aI : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field))
    (aP : ambientFixedAddSubgroup A P.field)
    (hsupport :
      fixedFieldInclusion A P.field (D.maximalUnramifiedField L) P.above aP =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI)
    (hfixed :
      D.frobeniusQuotientAction A K.field L hLK φ.1
          (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK) aI) :
    ∃ aK : ambientFixedAddSubgroup A K.field,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK = aI := by
  let hPfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) := P.finite
  let f : K.field.toSubgroup := Quotient.out φ.1
  have hfφ :
      (QuotientGroup.mk f :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = φ.1 :=
    Quotient.out_eq' φ.1
  have hfDegree : D.normalizedDegree K f =
      Multiplicative.ofAdd (1 : ZHat) := by
    calc
      D.normalizedDegree K f =
          D.extensionNormalizedDegree K L hLK (QuotientGroup.mk f) := rfl
      _ = D.extensionNormalizedDegree K L hLK φ.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hfφ
      _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK φ :=
        D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ
      _ = Multiplicative.ofAdd (1 : ZHat) := by simp [hφ]
  have hfFixed : A.ρ f.1 aI.1 = aI.1 := by
    rw [← hfφ] at hfixed
    exact congrArg Subtype.val hfixed
  have hfPowFixed (n : ℕ) : A.ρ (f.1 ^ n) aI.1 = aI.1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, map_mul]
        change A.ρ (f.1 ^ n) (A.ρ f.1 aI.1) = aI.1
        rw [hfFixed, ih]
  have hsval : aP.1 = aI.1 := congrArg Subtype.val hsupport
  have hKfixed (k : K.field.toSubgroup) : A.ρ k.1 aI.1 = aI.1 := by
    obtain ⟨q, hqk⟩ := D.frobeniusRestriction_surjective K P.field P.below
      (QuotientGroup.mk k)
    obtain ⟨n, _hn, hqDegree⟩ := q.2
    let t : K.field.toSubgroup := Quotient.out q.1
    have htq :
        (QuotientGroup.mk t :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field P.field P.below) = q.1 :=
      Quotient.out_eq' q.1
    have htDegree : D.normalizedDegree K t =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n := by
      calc
        D.normalizedDegree K t =
            D.extensionNormalizedDegree K P.field P.below
              (QuotientGroup.mk t) := rfl
        _ = D.extensionNormalizedDegree K P.field P.below q.1 :=
          congrArg (D.extensionNormalizedDegree K P.field P.below) htq
        _ = _ := hqDegree
    let z : K.field.toSubgroup := t⁻¹ * f ^ n
    have hzInertia : z ∈ D.fieldInertiaWithin K.field := by
      rw [← D.normalizedDegree_ker K]
      change D.normalizedDegree K z = 1
      rw [map_mul, map_inv, map_pow, htDegree, hfDegree]
      simp
    let zI : (D.maximalUnramifiedField K.field).toSubgroup :=
      ⟨z.1, ⟨z.2, hzInertia⟩⟩
    have hzFixed : A.ρ z.1 aI.1 = aI.1 := aI.2 zI
    have htFixed : A.ρ t.1 aI.1 = aI.1 := by
      calc
        A.ρ t.1 aI.1 = A.ρ t.1 (A.ρ z.1 aI.1) :=
          congrArg (A.ρ t.1) hzFixed.symm
        _ = A.ρ (t.1 * z.1) aI.1 := by rw [map_mul]; rfl
        _ = A.ρ (f.1 ^ n) aI.1 := by simp [z]
        _ = aI.1 := hfPowFixed n
    have htk :
        (QuotientGroup.mk t :
          K.field.toSubgroup ⧸ extensionSubgroup K.field P.field P.below) =
        QuotientGroup.mk k := by
      calc
        QuotientGroup.mk t =
            D.extensionRestriction K.field P.field P.below (QuotientGroup.mk t) := rfl
        _ = D.extensionRestriction K.field P.field P.below q.1 :=
          congrArg (D.extensionRestriction K.field P.field P.below) htq
        _ = QuotientGroup.mk k := hqk
    have hrel : t⁻¹ * k ∈ extensionSubgroup K.field P.field P.below :=
      QuotientGroup.eq.mp htk
    let rP : P.field.toSubgroup := ⟨(t⁻¹ * k).1, hrel⟩
    have hrval : rP.1 = (t⁻¹ * k).1 := rfl
    have hrval' : rP.1 = t.1⁻¹ * k.1 := hrval
    have hrFixed : A.ρ (t.1⁻¹ * k.1) aI.1 = aI.1 := by
      rw [← hsval, ← hrval']
      exact aP.2 rP
    calc
      A.ρ k.1 aI.1 = A.ρ (t.1 * (t.1⁻¹ * k.1)) aI.1 := by simp
      _ = A.ρ t.1 (A.ρ (t.1⁻¹ * k.1) aI.1) := by rw [map_mul]; rfl
      _ = A.ρ t.1 aI.1 := by rw [hrFixed]
      _ = aI.1 := htFixed
  let aK : ambientFixedAddSubgroup A K.field := ⟨aI.1, hKfixed⟩
  refine ⟨aK, ?_⟩
  apply Subtype.ext
  rfl

end DegreeData

end representationDescent

end

end ClassFormation
