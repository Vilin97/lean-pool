/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
public import LeanPool.Stafford38.Stafford38.Weyl.Symplectic
public import LeanPool.Stafford38.Stafford38.Weyl.LeadingSymbol
public import LeanPool.Stafford38.Stafford38.Characteristic.LinearAction


/-!
# Bernstein-symbol compatibility for linear Weyl changes

An algebra map whose generator images have Bernstein degree one preserves the
Bernstein filtration. Its action on every principal component is obtained by
commutatively substituting the degree-one principal symbols of those images.
For a symplectic linear Weyl map, this induced substitution is exactly the
phase-space linear action defined in `Characteristic.LinearAction`.
-/

@[expose] public section

namespace Stafford38.WeylSymbolCompatibility

open Stafford
open AlgebraicAnalysis
open Stafford38.Characteristic
open Stafford38.CharacteristicLinearAction
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW
open Stafford38.WeylSymplectic

noncomputable section

universe u
variable (k : Type u) [Field k]

theorem normalForm_linearCombination {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    presentedNormalFormLinearEquiv k n
        (freeWeylLinearCombination M
          (freeWeylGenerator (standardForm k n)) i) =
      symbolLinearCombination k M i := by
  calc
    _ = presentedNormalFormLinearEquiv k n
        (∑ j, (M i j) • freeWeylGenerator (standardForm k n) j) := by
      simp only [freeWeylLinearCombination, Algebra.smul_def]
    _ = ∑ j, (M i j) • MvPolynomial.X j := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, presentedNormalFormLinearEquiv_generator]
    _ = _ := by
      simp [symbolLinearCombination, Algebra.smul_def]

theorem linearCombination_mem_bernsteinPiece {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    freeWeylLinearCombination M
        (freeWeylGenerator (standardForm k n)) i ∈
      bernsteinPiece k n 1 := by
  rw [freeWeylLinearCombination]
  apply Submodule.sum_mem
  intro j hj
  rw [← Algebra.smul_def]
  apply Submodule.smul_mem
  rw [bernsteinPiece, mem_presentedWeightPiece,
    presentedNormalFormLinearEquiv_generator]
  intro m hm
  simp only [MvPolynomial.coeff_X, ne_eq, ite_eq_right_iff] at hm
  by_contra hweight
  exact hm (by
    intro h
    subst m
    simp [monomialWeight, bernsteinWeight] at hweight)

theorem principal_linearCombination {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    presentedPrincipalComponent k (@bernsteinWeight n) 1
        (freeWeylLinearCombination M
          (freeWeylGenerator (standardForm k n)) i) =
      symbolLinearCombination k M i := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, normalForm_linearCombination]
  rw [symbolLinearCombination, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [MvPolynomial.weightedHomogeneousComponent_C_mul]
  congr 1
  conv_lhs => rw [← pow_one (MvPolynomial.X j), MvPolynomial.X_pow_eq_monomial]
  conv_rhs => rw [← pow_one (MvPolynomial.X j), MvPolynomial.X_pow_eq_monomial]
  rw [weightedHomogeneousComponent_monomial]
  simp [monomialWeight, bernsteinWeight]

theorem one_mem_bernsteinPiece (r : ℕ) :
    (1 : PresentedWeyl k r) ∈ bernsteinPiece k r 0 := by
  rw [bernsteinPiece, mem_presentedWeightPiece,
    presentedNormalFormLinearEquiv_one]
  intro m hm
  simp only [MvPolynomial.coeff_one, ne_eq, ite_eq_right_iff] at hm
  by_contra hweight
  exact hm (by
    intro h
    subst m
    simp [monomialWeight] at hweight)

theorem pow_mem_bernsteinPiece {r : ℕ} {x : PresentedWeyl k r}
    (hx : x ∈ bernsteinPiece k r 1) :
    ∀ a : ℕ, x ^ a ∈ bernsteinPiece k r a
  | 0 => by simpa using one_mem_bernsteinPiece k r
  | a + 1 => by
      rw [pow_succ]
      simpa [Nat.add_comm] using
        mul_mem_bernsteinPiece k (pow_mem_bernsteinPiece hx a) hx

theorem algHom_orderedMonomial_mem_bernstein
    {r : ℕ} (f : PresentedWeyl k 0 →ₐ[k] PresentedWeyl k r)
    (_hgen : ∀ i : PhaseVar 0,
      f (freeWeylGenerator (standardForm k 0) i) ∈
        bernsteinPiece k r 1)
    (a p : Fin 0 → ℕ) :
    f (presentedOrderedMonomial k 0 a p) ∈
      bernsteinPiece k r
        (monomialWeight (@bernsteinWeight 0) (phaseExponent a p)) := by
  simp only [presentedOrderedMonomial, map_one]
  have hw : monomialWeight (@bernsteinWeight 0) (phaseExponent a p) = 0 := by
    have hphase : phaseExponent a p = 0 := by
      ext i
      cases i with
      | inl i => exact Fin.elim0 i
      | inr i => exact Fin.elim0 i
    rw [hphase]
    rfl
  rw [hw]
  exact one_mem_bernsteinPiece k r

theorem algHom_orderedMonomial_mem_bernstein_succ
    {n r : ℕ}
    (ih : ∀ (f : PresentedWeyl k n →ₐ[k] PresentedWeyl k r),
      (∀ i : PhaseVar n,
        f (freeWeylGenerator (standardForm k n) i) ∈
          bernsteinPiece k r 1) →
      ∀ (a p : Fin n → ℕ),
        f (presentedOrderedMonomial k n a p) ∈
          bernsteinPiece k r
            (monomialWeight (@bernsteinWeight n) (phaseExponent a p)))
    (f : PresentedWeyl k (n + 1) →ₐ[k] PresentedWeyl k r)
    (hgen : ∀ i : PhaseVar (n + 1),
      f (freeWeylGenerator (standardForm k (n + 1)) i) ∈
        bernsteinPiece k r 1)
    (a p : Fin (n + 1) → ℕ) :
    f (presentedOrderedMonomial k (n + 1) a p) ∈
      bernsteinPiece k r
        (monomialWeight (@bernsteinWeight (n + 1)) (phaseExponent a p)) := by
  let fold : PresentedWeyl k n →ₐ[k] PresentedWeyl k r :=
    f.comp (previousWeylEmbedding k n)
  have hfold : ∀ i : PhaseVar n,
      fold (freeWeylGenerator (standardForm k n) i) ∈
        bernsteinPiece k r 1 := by
    intro i
    simpa [fold, oldGenerator] using hgen (oldIndex i)
  have hold := ih fold hfold (fun i => a i.succ) (fun i => p i.succ)
  have hx := pow_mem_bernsteinPiece k (hgen (.inl 0)) (a 0)
  have hp := pow_mem_bernsteinPiece k (hgen (.inr 0)) (p 0)
  have hmul := mul_mem_bernsteinPiece k
    (mul_mem_bernsteinPiece k hold hx) hp
  change f ((previousWeylEmbedding k n)
      (presentedOrderedMonomial k n (fun i => a i.succ) (fun i => p i.succ))) *
      f (presentedCoordinate k n) ^ a 0 *
      f (presentedMomentum k n) ^ p 0 ∈ _ at hmul
  rw [presentedOrderedMonomial, map_mul, map_mul, map_pow, map_pow]
  rw [monomialWeight_phaseExponent_succ_bernstein]
  simpa [fold, add_assoc] using hmul

theorem algHom_orderedMonomial_mem_bernstein_all {r : ℕ} :
    ∀ (n : ℕ) (f : PresentedWeyl k n →ₐ[k] PresentedWeyl k r),
      (∀ i : PhaseVar n,
        f (freeWeylGenerator (standardForm k n) i) ∈
          bernsteinPiece k r 1) →
      ∀ (a p : Fin n → ℕ),
        f (presentedOrderedMonomial k n a p) ∈
          bernsteinPiece k r
            (monomialWeight (@bernsteinWeight n) (phaseExponent a p))
  | 0 => algHom_orderedMonomial_mem_bernstein k
  | n + 1 => algHom_orderedMonomial_mem_bernstein_succ k
      (algHom_orderedMonomial_mem_bernstein_all n)

theorem algHom_preserves_bernsteinPiece {n r N : ℕ}
    (f : PresentedWeyl k n →ₐ[k] PresentedWeyl k r)
    (hgen : ∀ i : PhaseVar n,
      f (freeWeylGenerator (standardForm k n) i) ∈
        bernsteinPiece k r 1)
    {z : PresentedWeyl k n} (hz : z ∈ bernsteinPiece k n N) :
  f z ∈ bernsteinPiece k r N := by
  rw [bernsteinPiece, presentedWeightPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := hb
      rw [presentedPBWBasis_apply]
      have h := algHom_orderedMonomial_mem_bernstein_all k n f hgen
        (fun i => m (.inl i)) (fun i => m (.inr i))
      rw [phaseExponent_split] at h
      exact presentedWeightPiece_mono k bernsteinWeight hm h
  | zero =>
      rw [map_zero]
      exact (bernsteinPiece k r N).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (bernsteinPiece k r N).add_mem ihx ihy
  | smul c x hx ih =>
      rw [map_smul]
      exact (bernsteinPiece k r N).smul_mem c ih

theorem standardSymplecticAlgHom_preserves_bernsteinPiece {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    {z : PresentedWeyl k n} (hz : z ∈ bernsteinPiece k n N) :
    standardSymplecticAlgHom k M hM z ∈ bernsteinPiece k n N := by
  exact algHom_preserves_bernsteinPiece k
    (standardSymplecticAlgHom k M hM)
    (fun i => by
      rw [standardSymplecticAlgHom_generator]
      exact linearCombination_mem_bernsteinPiece k M i) hz

theorem phaseMonomial_succ_decompose {n : ℕ}
    (a p : Fin (n + 1) → ℕ) :
    MvPolynomial.monomial (phaseExponent a p) (1 : k) =
      MvPolynomial.rename oldIndex
          (MvPolynomial.monomial
            (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) 1) *
        MvPolynomial.X (.inl (0 : Fin (n + 1))) ^ a 0 *
        MvPolynomial.X (.inr (0 : Fin (n + 1))) ^ p 0 := by
  rw [phaseExponent_succ_eq_extend, extendPhaseExponent,
    MvPolynomial.rename_monomial,
    MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial]
  simp [add_comm, add_left_comm, add_assoc]

theorem principal_one_bernstein (r : ℕ) :
    presentedPrincipalComponent k (@bernsteinWeight r) 0
        (1 : PresentedWeyl k r) = 1 := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, presentedNormalFormLinearEquiv_one]
  change MvPolynomial.weightedHomogeneousComponent (@bernsteinWeight r) 0
      (MvPolynomial.monomial (0 : PhaseVar r →₀ ℕ) (1 : k)) = 1
  rw [weightedHomogeneousComponent_monomial]
  simp [monomialWeight]

theorem pow_principal_bernstein {r : ℕ} {x : PresentedWeyl k r}
    (hx : x ∈ bernsteinPiece k r 1) :
    ∀ a : ℕ,
      presentedPrincipalComponent k (@bernsteinWeight r) a (x ^ a) =
        (presentedPrincipalComponent k (@bernsteinWeight r) 1 x) ^ a
  | 0 => by simpa using principal_one_bernstein k r
  | a + 1 => by
      rw [pow_succ, pow_succ, ← pow_principal_bernstein hx a]
      simpa [Nat.add_comm] using
        presentedPrincipalComponent_mul_bernstein k
          (pow_mem_bernsteinPiece k hx a) hx

theorem algHom_orderedMonomial_principal_zero
    {r : ℕ} (f : PresentedWeyl k 0 →ₐ[k] PresentedWeyl k r)
    (g : PhaseVar 0 → SymbolRing k r)
    (a p : Fin 0 → ℕ) :
    presentedPrincipalComponent k (@bernsteinWeight r)
        (monomialWeight (@bernsteinWeight 0) (phaseExponent a p))
        (f (presentedOrderedMonomial k 0 a p)) =
      MvPolynomial.aeval g
        (MvPolynomial.monomial (phaseExponent a p) (1 : k)) := by
  have hphase : phaseExponent a p = 0 := by
    ext i
    cases i with
    | inl i => exact Fin.elim0 i
    | inr i => exact Fin.elim0 i
  rw [hphase]
  simp [presentedOrderedMonomial, principal_one_bernstein, monomialWeight]

theorem algHom_orderedMonomial_principal_succ
    {n r : ℕ}
    (ih : ∀ (f : PresentedWeyl k n →ₐ[k] PresentedWeyl k r)
      (_hgen : ∀ i : PhaseVar n,
        f (freeWeylGenerator (standardForm k n) i) ∈
          bernsteinPiece k r 1)
      (g : PhaseVar n → SymbolRing k r),
      (∀ i,
        presentedPrincipalComponent k (@bernsteinWeight r) 1
            (f (freeWeylGenerator (standardForm k n) i)) = g i) →
      ∀ (a p : Fin n → ℕ),
        presentedPrincipalComponent k (@bernsteinWeight r)
            (monomialWeight (@bernsteinWeight n) (phaseExponent a p))
            (f (presentedOrderedMonomial k n a p)) =
          MvPolynomial.aeval g
            (MvPolynomial.monomial (phaseExponent a p) (1 : k)))
    (f : PresentedWeyl k (n + 1) →ₐ[k] PresentedWeyl k r)
    (hgen : ∀ i : PhaseVar (n + 1),
      f (freeWeylGenerator (standardForm k (n + 1)) i) ∈
        bernsteinPiece k r 1)
    (g : PhaseVar (n + 1) → SymbolRing k r)
    (hprincipal : ∀ i,
      presentedPrincipalComponent k (@bernsteinWeight r) 1
          (f (freeWeylGenerator (standardForm k (n + 1)) i)) = g i)
    (a p : Fin (n + 1) → ℕ) :
    presentedPrincipalComponent k (@bernsteinWeight r)
        (monomialWeight (@bernsteinWeight (n + 1)) (phaseExponent a p))
        (f (presentedOrderedMonomial k (n + 1) a p)) =
      MvPolynomial.aeval g
        (MvPolynomial.monomial (phaseExponent a p) (1 : k)) := by
  let fold : PresentedWeyl k n →ₐ[k] PresentedWeyl k r :=
    f.comp (previousWeylEmbedding k n)
  let gold : PhaseVar n → SymbolRing k r := fun i => g (oldIndex i)
  have hfold : ∀ i : PhaseVar n,
      fold (freeWeylGenerator (standardForm k n) i) ∈
        bernsteinPiece k r 1 := by
    intro i
    simpa [fold, oldGenerator] using hgen (oldIndex i)
  have hfoldprincipal : ∀ i,
      presentedPrincipalComponent k (@bernsteinWeight r) 1
          (fold (freeWeylGenerator (standardForm k n) i)) = gold i := by
    intro i
    simpa [fold, gold, oldGenerator] using hprincipal (oldIndex i)
  let aold : Fin n → ℕ := fun i => a i.succ
  let pold : Fin n → ℕ := fun i => p i.succ
  let d := monomialWeight (@bernsteinWeight n) (phaseExponent aold pold)
  have holdmem := algHom_orderedMonomial_mem_bernstein_all k n fold hfold aold pold
  have holdprincipal := ih fold hfold gold hfoldprincipal aold pold
  have hx := hgen (.inl 0)
  have hp := hgen (.inr 0)
  have hxa := pow_mem_bernsteinPiece k hx (a 0)
  have hpp := pow_mem_bernsteinPiece k hp (p 0)
  have hfirst := presentedPrincipalComponent_mul_bernstein k holdmem hxa
  rw [pow_principal_bernstein k hx] at hfirst
  have hfirstmem := mul_mem_bernsteinPiece k holdmem hxa
  have hsecond := presentedPrincipalComponent_mul_bernstein k hfirstmem hpp
  rw [pow_principal_bernstein k hp, hfirst, holdprincipal,
    hprincipal (.inl 0), hprincipal (.inr 0)] at hsecond
  have hf : f (presentedOrderedMonomial k (n + 1) a p) =
      fold (presentedOrderedMonomial k n aold pold) *
        f (presentedCoordinate k n) ^ a 0 *
        f (presentedMomentum k n) ^ p 0 := by
    rw [presentedOrderedMonomial, map_mul, map_mul, map_pow, map_pow]
    rfl
  rw [hf, monomialWeight_phaseExponent_succ_bernstein]
  change presentedPrincipalComponent k (@bernsteinWeight r)
      (d + a 0 + p 0)
      (fold (presentedOrderedMonomial k n aold pold) *
        f (presentedCoordinate k n) ^ a 0 *
        f (presentedMomentum k n) ^ p 0) = _
  rw [phaseMonomial_succ_decompose]
  simp only [map_mul, map_pow, MvPolynomial.aeval_X]
  rw [MvPolynomial.aeval_rename]
  exact hsecond

theorem algHom_orderedMonomial_principal_all {r : ℕ} :
    ∀ (n : ℕ) (f : PresentedWeyl k n →ₐ[k] PresentedWeyl k r)
      (_hgen : ∀ i : PhaseVar n,
        f (freeWeylGenerator (standardForm k n) i) ∈
          bernsteinPiece k r 1)
      (g : PhaseVar n → SymbolRing k r),
      (∀ i,
        presentedPrincipalComponent k (@bernsteinWeight r) 1
            (f (freeWeylGenerator (standardForm k n) i)) = g i) →
      ∀ (a p : Fin n → ℕ),
        presentedPrincipalComponent k (@bernsteinWeight r)
            (monomialWeight (@bernsteinWeight n) (phaseExponent a p))
            (f (presentedOrderedMonomial k n a p)) =
          MvPolynomial.aeval g
            (MvPolynomial.monomial (phaseExponent a p) (1 : k))
  | 0 => fun f _ g _ => algHom_orderedMonomial_principal_zero k f g
  | n + 1 => algHom_orderedMonomial_principal_succ k
      (algHom_orderedMonomial_principal_all n)

theorem algHom_principal_compatibility {n r N : ℕ}
    (f : PresentedWeyl k n →ₐ[k] PresentedWeyl k r)
    (hgen : ∀ i : PhaseVar n,
      f (freeWeylGenerator (standardForm k n) i) ∈
        bernsteinPiece k r 1)
    (g : PhaseVar n → SymbolRing k r)
    (hprincipal : ∀ i,
      presentedPrincipalComponent k (@bernsteinWeight r) 1
          (f (freeWeylGenerator (standardForm k n) i)) = g i)
    {z : PresentedWeyl k n} (hz : z ∈ bernsteinPiece k n N) :
    presentedPrincipalComponent k (@bernsteinWeight r) N (f z) =
      MvPolynomial.aeval g
        (presentedPrincipalComponent k (@bernsteinWeight n) N z) := by
  rw [bernsteinPiece, presentedWeightPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := hb
      let d := monomialWeight (@bernsteinWeight n) m
      have hmapmem : f (presentedPBWBasis k n m) ∈ bernsteinPiece k r d := by
        rw [presentedPBWBasis_apply]
        have h := algHom_orderedMonomial_mem_bernstein_all k n f hgen
          (fun i => m (.inl i)) (fun i => m (.inr i))
        rw [phaseExponent_split] at h
        exact h
      by_cases hd : d = N
      · subst N
        rw [presentedPrincipalComponent_basis, ite_eq_left rfl,
          presentedPBWBasis_apply]
        have h := algHom_orderedMonomial_principal_all k n f hgen g hprincipal
          (fun i => m (.inl i)) (fun i => m (.inr i))
        rw [phaseExponent_split] at h
        exact h
      · have hdlt : d < N := lt_of_le_of_ne hm hd
        rw [presentedPrincipalComponent_eq_zero_of_mem_of_lt k
          (@bernsteinWeight r) (f (presentedPBWBasis k n m)) hmapmem hdlt,
          presentedPrincipalComponent_basis, ite_eq_right hd, map_zero]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simp only [map_add]
      rw [ihx, ihy]
  | smul c x hx ih =>
      simp only [map_smul]
      rw [ih]

theorem standardSymplecticAlgHom_principal_compatibility {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    {z : PresentedWeyl k n} (hz : z ∈ bernsteinPiece k n N) :
    presentedPrincipalComponent k (@bernsteinWeight n) N
        (standardSymplecticAlgHom k M hM z) =
      symbolLinearAlgHom k M
        (presentedPrincipalComponent k (@bernsteinWeight n) N z) := by
  exact algHom_principal_compatibility k
    (standardSymplecticAlgHom k M hM)
    (fun i => by
      rw [standardSymplecticAlgHom_generator]
      exact linearCombination_mem_bernsteinPiece k M i)
    (symbolLinearCombination k M)
    (fun i => by
      rw [standardSymplecticAlgHom_generator]
      exact principal_linearCombination k M i) hz

/- Exact statement pins for the two exported compatibility conclusions. -/
example {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    {z : PresentedWeyl k n} (hz : z ∈ bernsteinPiece k n N) :
    standardSymplecticAlgHom k M hM z ∈ bernsteinPiece k n N :=
  standardSymplecticAlgHom_preserves_bernsteinPiece k M hM hz

example {n N : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    {z : PresentedWeyl k n} (hz : z ∈ bernsteinPiece k n N) :
    presentedPrincipalComponent k (@bernsteinWeight n) N
        (standardSymplecticAlgHom k M hM z) =
      symbolLinearAlgHom k M
        (presentedPrincipalComponent k (@bernsteinWeight n) N z) :=
  standardSymplecticAlgHom_principal_compatibility k M hM hz


end
end Stafford38.WeylSymbolCompatibility
