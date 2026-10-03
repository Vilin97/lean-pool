/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.PrimitiveReduction
/-!
# Primitive irreducible reductions and Hensel factorization

This file isolates the common algebraic last step in the unique-extension
and factor-lifting criteria. The proof first proves that the reduction of every
primitive irreducible factor is either constant or has full degree and is a
power of one irreducible residual polynomial.  Unique factorization then
partitions the fraction-field irreducible factors along any coprime residual
factorization.
-/

@[expose] public section

noncomputable
section

open Polynomial

namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField

/-- The precise irreducible-factor input used in the last paragraph of the
proof of the unique-extension criterion.  The second clause is the factorization-free
form of saying that a nonconstant reduction is a scalar times a power of one
irreducible polynomial. -/
def PrimitiveIrreducibleReductionProperty
    {K : Type*} [Field K] (V : ValuationSubring K) : Prop :=
  ∀ Q : Polynomial V,
    Q.IsPrimitive → Irreducible (Q.map V.subtype) →
      let qbar := Q.map (IsLocalRing.residue V)
      (qbar.natDegree = 0 ∨ qbar.natDegree = Q.natDegree) ∧
        ∀ a b : Polynomial (IsLocalRing.ResidueField V),
          qbar = a * b → IsCoprime a b →
            a.natDegree = 0 ∨ b.natDegree = 0

/-- A primitive irreducible reduction satisfying the primitive factorization property divides
exactly one side of every coprime residual product that it divides. -/
theorem primitiveIrreducibleReduction_dvd_left_or_right_of_coprime
    {K : Type*} [Field K] (V : ValuationSubring K)
    (hproperty : PrimitiveIrreducibleReductionProperty V)
    (Q : Polynomial V) (hQprim : Q.IsPrimitive)
    (hQirr : Irreducible (Q.map V.subtype))
    (gbar hbar : Polynomial (IsLocalRing.ResidueField V))
    (hcoprime : IsCoprime gbar hbar)
    (hQdvd : Q.map (IsLocalRing.residue V) ∣ gbar * hbar) :
    Q.map (IsLocalRing.residue V) ∣ gbar ∨
      Q.map (IsLocalRing.residue V) ∣ hbar := by
  let qbar := Q.map (IsLocalRing.residue V)
  obtain ⟨q₁, q₂, hq₁g, hq₂h, hQfactor⟩ :=
    exists_dvd_and_dvd_of_dvd_mul hQdvd
  have hqcoprime : IsCoprime q₁ q₂ := by
    rcases hcoprime with ⟨A, B, hbez⟩
    obtain ⟨g', hg'⟩ := hq₁g
    obtain ⟨h', hh'⟩ := hq₂h
    refine ⟨A * g', B * h', ?_⟩
    calc
      (A * g') * q₁ + (B * h') * q₂ =
          A * (q₁ * g') + B * (q₂ * h') := by ring
      _ = A * gbar + B * hbar := by rw [← hg', ← hh']
      _ = 1 := hbez
  have hdegrees := (hproperty Q hQprim hQirr).2 q₁ q₂ hQfactor hqcoprime
  have hQbar0 : qbar ≠ 0 :=
    polynomial_residue_ne_zero_of_isPrimitive V hQprim
  have hqprod0 : q₁ * q₂ ≠ 0 := by
    rw [← hQfactor]
    exact hQbar0
  have hq₁0 : q₁ ≠ 0 := left_ne_zero_of_mul hqprod0
  have hq₂0 : q₂ ≠ 0 := right_ne_zero_of_mul hqprod0
  rcases hdegrees with hq₁deg | hq₂deg
  · right
    have hq₁unit : IsUnit q₁ := by
      rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree hq₁0, hq₁deg]
      rfl
    have hassoc : Associated (q₁ * q₂) q₂ :=
      associated_unit_mul_left q₂ q₁ hq₁unit
    change qbar ∣ hbar
    have hqfactor : qbar = q₁ * q₂ := hQfactor
    rw [hqfactor]
    exact hassoc.dvd_iff_dvd_left.mpr hq₂h
  · left
    have hq₂unit : IsUnit q₂ := by
      rw [Polynomial.isUnit_iff_degree_eq_zero,
        Polynomial.degree_eq_natDegree hq₂0, hq₂deg]
      rfl
    have hassoc : Associated (q₁ * q₂) q₁ :=
      associated_mul_unit_left q₁ q₂ hq₂unit
    change qbar ∣ gbar
    have hqfactor : qbar = q₁ * q₂ := hQfactor
    rw [hqfactor]
    exact hassoc.dvd_iff_dvd_left.mpr hq₁g

/-- Partition primitive irreducible factors along a coprime residual
factorization.  Factors with constant reduction are placed on the right;
therefore the left lifted factor has exactly the degree of the prescribed
left residual factor. -/
theorem partition_primitive_irreducible_factors_along_coprime_reduction
    {K : Type*} [Field K] (V : ValuationSubring K)
    (hproperty : PrimitiveIrreducibleReductionProperty V)
    (factors : Multiset (Polynomial V))
    (hfactors : ∀ Q ∈ factors,
      Q.IsPrimitive ∧ Irreducible (Q.map V.subtype))
    (gbar hbar : Polynomial (IsLocalRing.ResidueField V))
    (hproduct :
      (factors.map (fun Q => Q.map (IsLocalRing.residue V))).prod =
        gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ G H : Polynomial V,
      factors.prod = G * H ∧
        G.map (IsLocalRing.residue V) = gbar ∧
          H.map (IsLocalRing.residue V) = hbar ∧
            G.natDegree = gbar.natDegree := by
  classical
  induction factors using Multiset.induction_on generalizing gbar hbar with
  | empty =>
      have hgh : gbar * hbar = 1 := by simpa using hproduct.symm
      have hgunit : IsUnit gbar :=
        isUnit_iff_exists_inv'.2 ⟨hbar, by simpa [mul_comm] using hgh⟩
      obtain ⟨c, hcunit, hcg⟩ := Polynomial.isUnit_iff.mp hgunit
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective c
      have hares : IsLocalRing.residue V a = c := ha
      have haunit : IsUnit a :=
        (IsLocalRing.residue_ne_zero_iff_isUnit a).1
          (by simpa [hares] using hcunit.ne_zero)
      obtain ⟨ua, hua⟩ := haunit
      let G : Polynomial V := Polynomial.C a
      let H : Polynomial V := Polynomial.C (ua⁻¹ : Vˣ)
      have hGH : G * H = 1 := by
        change Polynomial.C a * Polynomial.C ((ua⁻¹ : Vˣ) : V) =
          Polynomial.C 1
        rw [← Polynomial.C_mul]
        congr 1
        rw [← hua]
        exact Units.mul_inv ua
      have hGmap : G.map (IsLocalRing.residue V) = gbar := by
        simpa [G, hares] using hcg
      have hHmap : H.map (IsLocalRing.residue V) = hbar := by
        apply mul_left_cancel₀ hgunit.ne_zero
        calc
          gbar * H.map (IsLocalRing.residue V) =
              G.map (IsLocalRing.residue V) *
                H.map (IsLocalRing.residue V) := by rw [hGmap]
          _ = (G * H).map (IsLocalRing.residue V) := by
            rw [Polynomial.map_mul]
          _ = 1 := by simp [hGH]
          _ = gbar * hbar := hgh.symm
      have hGunit : IsUnit G := by
        dsimp [G]
        rw [← hua]
        exact Polynomial.isUnit_C.mpr ua.isUnit
      refine ⟨G, H, ?_, hGmap, hHmap, ?_⟩
      · simpa using hGH.symm
      · rw [Polynomial.natDegree_eq_zero_of_isUnit hGunit,
          Polynomial.natDegree_eq_zero_of_isUnit hgunit]
  | cons Q factors ih =>
      have hQdata : Q.IsPrimitive ∧ Irreducible (Q.map V.subtype) :=
        hfactors Q (by simp)
      have htail : ∀ R ∈ factors,
          R.IsPrimitive ∧ Irreducible (R.map V.subtype) := by
        intro R hR
        exact hfactors R (by simp [hR])
      let qbar : Polynomial (IsLocalRing.ResidueField V) :=
        Q.map (IsLocalRing.residue V)
      have hQbar0 : qbar ≠ 0 :=
        polynomial_residue_ne_zero_of_isPrimitive V hQdata.1
      have hdegreeData := (hproperty Q hQdata.1 hQdata.2).1
      have hproduct' :
          qbar * (factors.map
            (fun R => R.map (IsLocalRing.residue V))).prod =
              gbar * hbar := by
        simpa [qbar] using hproduct
      have hQdvd : qbar ∣ gbar * hbar := by
        rw [← hproduct']
        exact dvd_mul_right _ _
      have hside :
          (qbar.natDegree = Q.natDegree ∧ qbar ∣ gbar) ∨
            qbar ∣ hbar := by
        rcases hdegreeData with hqconst | hqfull
        · right
          have hqunit : IsUnit qbar := by
            rw [Polynomial.isUnit_iff_degree_eq_zero,
              Polynomial.degree_eq_natDegree hQbar0, hqconst]
            rfl
          exact hqunit.dvd
        · rcases
            primitiveIrreducibleReduction_dvd_left_or_right_of_coprime
              V hproperty Q hQdata.1 hQdata.2 gbar hbar hcoprime hQdvd with
            hQg | hQh
          · exact Or.inl ⟨hqfull, hQg⟩
          · exact Or.inr hQh
      rcases hside with ⟨hQdegree, hQg⟩ | hQh
      · obtain ⟨g', hg'⟩ := hQg
        have hg'coprime : IsCoprime g' hbar := by
          rcases hcoprime with ⟨A, B, hbez⟩
          refine ⟨A * qbar, B, ?_⟩
          calc
            (A * qbar) * g' + B * hbar =
                A * (qbar * g') + B * hbar := by ring
            _ = A * gbar + B * hbar := by rw [← hg']
            _ = 1 := hbez
        have hrest :
            (factors.map
              (fun R => R.map (IsLocalRing.residue V))).prod =
                g' * hbar := by
          apply mul_left_cancel₀ hQbar0
          calc
            qbar * (factors.map
                (fun R => R.map (IsLocalRing.residue V))).prod =
                gbar * hbar := hproduct'
            _ = (qbar * g') * hbar := by rw [← hg']
            _ = qbar * (g' * hbar) := by ring
        obtain ⟨G, H, hfactorGH, hGbar, hHbar, hGdegree⟩ :=
          ih htail g' hbar hrest hg'coprime
        have hQ0 : Q ≠ 0 := hQdata.1.ne_zero
        have hg'0 : g' ≠ 0 := by
          have hrest0 :
              (factors.map
                (fun R => R.map (IsLocalRing.residue V))).prod ≠ 0 :=
            Multiset.prod_ne_zero (by
              intro hzeroMem
              rcases Multiset.mem_map.mp hzeroMem with ⟨R, hR, hRzero⟩
              exact
                (polynomial_residue_ne_zero_of_isPrimitive V (htail R hR).1)
                  hRzero)
          have hmul0 : g' * hbar ≠ 0 := by
            rw [← hrest]
            exact hrest0
          exact left_ne_zero_of_mul hmul0
        have hG0 : G ≠ 0 := by
          intro hzero
          rw [hzero] at hGbar
          exact hg'0 (by simpa using hGbar.symm)
        refine ⟨Q * G, H, ?_, ?_, hHbar, ?_⟩
        · simp only [Multiset.prod_cons, hfactorGH]
          ring
        · rw [Polynomial.map_mul, hGbar]
          exact hg'.symm
        · rw [Polynomial.natDegree_mul hQ0 hG0]
          calc
            Q.natDegree + G.natDegree =
                qbar.natDegree + g'.natDegree := by
              rw [hQdegree, hGdegree]
            _ = (qbar * g').natDegree :=
              (Polynomial.natDegree_mul hQbar0 hg'0).symm
            _ = gbar.natDegree := by rw [← hg']
      · obtain ⟨h', hh'⟩ := hQh
        have hh'coprime : IsCoprime gbar h' := by
          rcases hcoprime with ⟨A, B, hbez⟩
          refine ⟨A, B * qbar, ?_⟩
          calc
            A * gbar + (B * qbar) * h' =
                A * gbar + B * (qbar * h') := by ring
            _ = A * gbar + B * hbar := by rw [← hh']
            _ = 1 := hbez
        have hrest :
            (factors.map
              (fun R => R.map (IsLocalRing.residue V))).prod =
                gbar * h' := by
          apply mul_left_cancel₀ hQbar0
          calc
            qbar * (factors.map
                (fun R => R.map (IsLocalRing.residue V))).prod =
                gbar * hbar := hproduct'
            _ = gbar * (qbar * h') := by rw [← hh']
            _ = qbar * (gbar * h') := by ring
        obtain ⟨G, H, hfactorGH, hGbar, hHbar, hGdegree⟩ :=
          ih htail gbar h' hrest hh'coprime
        refine ⟨G, Q * H, ?_, hGbar, ?_, hGdegree⟩
        · simp only [Multiset.prod_cons, hfactorGH]
          ring
        · rw [Polynomial.map_mul, hHbar]
          exact hh'.symm

/-- The common last step of the unique-extension criterion and the factor-lifting criterion: the
construction's
primitive irreducible reduction property implies the exact degree-controlled
factorization form of Hensel's lemma from the primitive factorization definition. -/
theorem henselFactorization_of_primitiveIrreducibleReductionProperty
    {K : Type*} [Field K] (V : ValuationSubring K)
    (hproperty : PrimitiveIrreducibleReductionProperty V) :
    HenselFactorizationProperty V := by
  intro f gbar hbar hfbar hfactor hcoprime
  have hfprim : f.IsPrimitive :=
    polynomial_isPrimitive_of_residue_ne_zero hfbar
  obtain ⟨factors, hfactors, hassoc⟩ :=
    primitive_associated_prod_primitive_irreducible_map_factors V f hfprim
  obtain ⟨u, hu⟩ := hassoc
  let U : Polynomial V := (u : Polynomial V)
  let ubar : (Polynomial (IsLocalRing.ResidueField V))ˣ :=
    Units.map (Polynomial.mapRingHom (IsLocalRing.residue V)) u
  let hbar' : Polynomial (IsLocalRing.ResidueField V) :=
    hbar * (ubar⁻¹ :
      (Polynomial (IsLocalRing.ResidueField V))ˣ)
  have hmapU : U.map (IsLocalRing.residue V) =
      (ubar : Polynomial (IsLocalRing.ResidueField V)) := by
    rfl
  have humap :
      (factors.map
          (fun Q => Q.map (IsLocalRing.residue V))).prod *
          (ubar : Polynomial (IsLocalRing.ResidueField V)) =
        gbar * hbar := by
    have h := congrArg (Polynomial.map (IsLocalRing.residue V)) hu
    rw [Polynomial.map_mul, Polynomial.map_multiset_prod] at h
    change
      (factors.map
          (fun Q => Q.map (IsLocalRing.residue V))).prod *
          (ubar : Polynomial (IsLocalRing.ResidueField V)) =
        f.map (IsLocalRing.residue V) at h
    exact h.trans hfactor
  have hproduct :
      (factors.map
          (fun Q => Q.map (IsLocalRing.residue V))).prod =
        gbar * hbar' := by
    apply mul_right_cancel₀ ubar.ne_zero
    calc
      (factors.map
            (fun Q => Q.map (IsLocalRing.residue V))).prod *
          (ubar : Polynomial (IsLocalRing.ResidueField V)) =
          gbar * hbar := humap
      _ = (gbar * hbar') *
          (ubar : Polynomial (IsLocalRing.ResidueField V)) := by
        dsimp [hbar']
        simp [mul_assoc]
  have hcoprime' : IsCoprime gbar hbar' := by
    rcases hcoprime with ⟨A, B, hbez⟩
    refine ⟨A, B * (ubar : Polynomial (IsLocalRing.ResidueField V)), ?_⟩
    dsimp [hbar']
    calc
      A * gbar + (B * (ubar : Polynomial (IsLocalRing.ResidueField V))) *
          (hbar * (ubar⁻¹ :
            (Polynomial (IsLocalRing.ResidueField V))ˣ)) =
          A * gbar + B * hbar := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      _ = 1 := hbez
  obtain ⟨G, H₀, hGH₀, hGmap, hH₀map, hGdegree⟩ :=
    partition_primitive_irreducible_factors_along_coprime_reduction
      V hproperty factors hfactors gbar hbar' hproduct hcoprime'
  let H : Polynomial V := H₀ * U
  have hfactorGH : f = G * H := by
    calc
      f = factors.prod * U := hu.symm
      _ = (G * H₀) * U := by rw [hGH₀]
      _ = G * H := by simp [H, mul_assoc]
  have hHmap : H.map (IsLocalRing.residue V) = hbar := by
    change (H₀ * U).map (IsLocalRing.residue V) = hbar
    rw [Polynomial.map_mul, hH₀map, hmapU]
    dsimp [hbar']
    simp [mul_assoc]
  have hgh0 : gbar * hbar ≠ 0 := by
    rw [← hfactor]
    exact hfbar
  have hg0 : gbar ≠ 0 := left_ne_zero_of_mul hgh0
  have hh0 : hbar ≠ 0 := right_ne_zero_of_mul hgh0
  have hG0 : G ≠ 0 := by
    intro hzero
    rw [hzero] at hGmap
    exact hg0 (by simpa using hGmap.symm)
  have hH0 : H ≠ 0 := by
    intro hzero
    rw [hzero] at hHmap
    exact hh0 (by simpa using hHmap.symm)
  have hdegree : f.natDegree = G.natDegree + H.natDegree := by
    rw [hfactorGH, Polynomial.natDegree_mul hG0 hH0]
  have hHdegree : H.natDegree ≤ f.natDegree - gbar.natDegree := by
    rw [hGdegree] at hdegree
    omega
  exact ⟨G, H, hGdegree, hHdegree, hfactorGH, hGmap, hHmap⟩

end DiscreteValuationField

end
