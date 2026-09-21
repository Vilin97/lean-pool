/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduction
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation

/-!
# Finite-class reduction in a bounded Hahn integer part

LM24's open truncation and reduction at an Archimedean class preserve a cardinal-bounded Hahn
integer part. When the open truncation is nonzero, their product is the original series.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries

namespace HahnSeries.Nonpositive

variable {K G R : Type*} {κ : Cardinal}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R] [Fact (ℵ₀ < κ)]

private theorem support_tau_subset (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    ((tau (K := K) c x : Nonpositive G R) : R⟦G⟧).support ⊆ (x : R⟦G⟧).support := by
  intro g hg
  by_cases hball : g ∈ ball K c
  · rw [HahnSeries.mem_support, coeff_tau_of_mem c x hball] at hg
    exact hg
  · rw [HahnSeries.mem_support, coeff_tau_of_not_mem c x hball] at hg
    exact (hg rfl).elim

/-- The open truncation `τ_σ(x)`, regarded as an element of the bounded integer part. -/
def tauIntegerPart (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z :=
  ⟨⟨((tau (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) :
      Nonpositive G R) : R⟦G⟧),
    (HahnSeries.cardSupp_mono (support_tau_subset c _)).trans_lt
      (CardSuppLTTruncationIntegerPart.cardSupp_toNonpositiveRingHom_lt Z x)⟩, by
    rw [mem_cardSuppLTTruncationIntegerPart]
    refine ⟨support_subset _, ?_⟩
    rw [coeff_tau_of_mem c _ (zero_mem _),
      CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
    exact ((mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2).2⟩

@[simp]
theorem toNonpositive_tauIntegerPart (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z (tauIntegerPart (K := K) c Z x) =
      tau (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  rfl

/-- The coefficient at zero of LM24's reduction is one when the open truncation is nonzero. -/
theorem coeff_zero_rho_of_tau_ne_zero (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R) (htau : tau (K := K) c x ≠ 0) :
    ((rho u c x : Nonpositive G R) : R⟦G⟧).coeff 0 = 1 := by
  rw [rho_of_tau_ne_zero u c x htau]
  exact coeff_zero_reductionQuotient u c x _

/-- LM24's reduction `ρ_σ(x)`, regarded as an element of the bounded integer part. -/
def rhoIntegerPart (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hT : T (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) =
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)
    (htau : tau (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) ≠ 0) :
    cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z := by
  refine ⟨(x : CardSuppLTField (G := G) (R := R) (κ := κ)) /
    (tauIntegerPart (K := K) c Z x : CardSuppLTField (G := G) (R := R) (κ := κ)), ?_⟩
  have hτ : ((tauIntegerPart (K := K) c Z x :
      CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) ≠ 0 := by
    intro h
    apply htau
    apply Subtype.ext
    exact h
  have hq : (((x : CardSuppLTField (G := G) (R := R) (κ := κ)) /
      (tauIntegerPart (K := K) c Z x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
        CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
      ((rho u c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) :
        Nonpositive G R) : R⟦G⟧) := by
    have hmul := reductionQuotient_mul_tau u c
      (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)
      (fun hzero ↦ htau ((tauBall_eq_zero_iff c _).mp hzero))
    rw [← rho_of_tau_ne_zero u c _ htau, hT] at hmul
    have hmul' := congrArg (fun q : Nonpositive G R ↦ (q : R⟦G⟧)) hmul
    simp only [Subring.coe_mul] at hmul'
    rw [Subfield.coe_div, div_eq_iff hτ]
    change ((x : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
      ((rho u c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) :
        Nonpositive G R) : R⟦G⟧) *
        ((tau (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) :
          Nonpositive G R) : R⟦G⟧)
    rw [hmul', CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  rw [mem_cardSuppLTTruncationIntegerPart, hq]
  refine ⟨support_subset _, ?_⟩
  rw [coeff_zero_rho_of_tau_ne_zero u c _ htau]
  exact Z.one_mem

theorem toNonpositive_rhoIntegerPart (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hT : T (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) =
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)
    (htau : tau (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) ≠ 0) :
    CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z (rhoIntegerPart u c Z x hT htau) =
      rho u c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) := by
  apply Subtype.ext
  rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
  have hτ : ((tauIntegerPart (K := K) c Z x :
      CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) ≠ 0 := by
    intro h
    apply htau
    apply Subtype.ext
    exact h
  have hmul := reductionQuotient_mul_tau u c
    (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)
    (fun hzero ↦ htau ((tauBall_eq_zero_iff c _).mp hzero))
  rw [← rho_of_tau_ne_zero u c _ htau, hT] at hmul
  have hmul' := congrArg (fun q : Nonpositive G R ↦ (q : R⟦G⟧)) hmul
  simp only [Subring.coe_mul] at hmul'
  change (((x : CardSuppLTField (G := G) (R := R) (κ := κ)) /
    (tauIntegerPart (K := K) c Z x : CardSuppLTField (G := G) (R := R) (κ := κ)) :
      CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) = _
  rw [Subfield.coe_div, div_eq_iff hτ]
  change ((x : CardSuppLTField (G := G) (R := R) (κ := κ)) : R⟦G⟧) =
    ((rho u c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) :
      Nonpositive G R) : R⟦G⟧) *
      ((tau (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) :
        Nonpositive G R) : R⟦G⟧)
  rw [hmul', CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]

/-- The factorisation `x = ρ_σ(x) τ_σ(x)` inside the bounded integer part. -/
theorem rhoIntegerPart_mul_tauIntegerPart (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (hT : T (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) =
      CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x)
    (htau : tau (K := K) c (CardSuppLTTruncationIntegerPart.toNonpositiveRingHom Z x) ≠ 0) :
    rhoIntegerPart u c Z x hT htau * tauIntegerPart (K := K) c Z x = x := by
  apply CardSuppLTTruncationIntegerPart.toNonpositiveRingHom_injective Z
  rw [map_mul, toNonpositive_rhoIntegerPart, toNonpositive_tauIntegerPart,
    rho_of_tau_ne_zero u c _ htau, reductionQuotient_mul_tau, hT]

end HahnSeries.Nonpositive
