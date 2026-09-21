/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedCharacterization

/-!
# Divisibility after LM24 reduction

This module proves the reduction-algebra core of LM24, Proposition 8.2.8. At the leading class
of a reduced nonconstant series `b`, divisibility of the closed truncation `T(c)` by `b` is
equivalent to divisibility of `rho(c)` by `b`. Proposition 8.2.1, which identifies divisibility
of `c` with divisibility of `T(c)`, is the remaining ambient-series bridge.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass HahnEmbedding

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

private theorem reductionQuotient_dvd_T
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (htau : tau (K := K) c x ≠ 0) :
    reductionQuotient u c x
        (fun hzero ↦ htau ((tauBall_eq_zero_iff c x).mp hzero)) ∣
      T (K := K) c x := by
  refine ⟨tau (K := K) c x, ?_⟩
  exact (reductionQuotient_mul_tau u c x
    (fun hzero ↦ htau ((tauBall_eq_zero_iff c x).mp hzero))).symm

/-- LM24's reduction always divides the corresponding closed-class truncation. -/
theorem rho_dvd_T (u : HahnEmbedding.ArchimedeanStrata K G)
    (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    rho u c x ∣ T (K := K) c x := by
  by_cases htau : tau (K := K) c x = 0
  · rw [rho_of_tau_eq_zero u c x htau]
  · rw [rho_of_tau_ne_zero u c x htau]
    exact reductionQuotient_dvd_T u c x htau

/-- The reduction-algebra core of LM24, Proposition 8.2.8. For a reduced nonconstant `b`,
divisibility of `T(c)` by `b` is equivalent to divisibility of `rho(c)` by `b`. -/
theorem dvd_T_iff_dvd_rho_leadingClass
    (u : HahnEmbedding.ArchimedeanStrata K G) (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) (hbReduced : IsReduced b)
    (c : Nonpositive G R) :
    b ∣ T (K := K) (leadingClass b horder) c ↔
      b ∣ rho u (leadingClass b horder) c := by
  let sigma := leadingClass b horder
  have hTb : T (K := K) sigma b = b := T_leadingClass b horder
  have htaub : tau (K := K) sigma b = 0 ∨ tau (K := K) sigma b = 1 :=
    (isReduced_iff_tau_leadingClass_eq_zero_or_one b hb0 horder).mp hbReduced
  constructor
  · rintro ⟨e, hce⟩
    have hTe : T (K := K) sigma e = e := by
      apply mul_left_cancel₀ hb0
      calc
        b * T (K := K) sigma e =
            T (K := K) sigma b * T (K := K) sigma e := by rw [hTb]
        _ = T (K := K) sigma (b * e) :=
          ((T (K := K) sigma).map_mul b e).symm
        _ = T (K := K) sigma (T (K := K) sigma c) := by rw [hce]
        _ = T (K := K) sigma c := T_T sigma c
        _ = b * e := hce
    have htauMul : tau (K := K) sigma c =
        tau (K := K) sigma b * tau (K := K) sigma e := by
      calc
        tau (K := K) sigma c =
            tau (K := K) sigma (T (K := K) sigma c) := (tau_T sigma c).symm
        _ = tau (K := K) sigma (b * e) := by rw [hce]
        _ = tau (K := K) sigma b * tau (K := K) sigma e :=
          (tau (K := K) sigma).map_mul b e
    by_cases htauc : tau (K := K) sigma c = 0
    · rw [rho_of_tau_eq_zero u sigma c htauc]
      exact ⟨e, hce⟩
    · have htaue : tau (K := K) sigma e ≠ 0 := by
        intro he
        apply htauc
        rw [htauMul, he, mul_zero]
      have htaubOne : tau (K := K) sigma b = 1 := htaub.resolve_left (by
        intro hb
        apply htauc
        rw [htauMul, hb, zero_mul])
      have htaucEq : tau (K := K) sigma c = tau (K := K) sigma e := by
        rw [htauMul, htaubOne, one_mul]
      rw [rho_of_tau_ne_zero u sigma c htauc]
      let qC := reductionQuotient u sigma c
        (fun hzero ↦ htauc ((tauBall_eq_zero_iff sigma c).mp hzero))
      let qE := reductionQuotient u sigma e
        (fun hzero ↦ htaue ((tauBall_eq_zero_iff sigma e).mp hzero))
      refine ⟨qE, ?_⟩
      apply mul_right_cancel₀ htauc
      have hqC : qC * tau (K := K) sigma c = T (K := K) sigma c :=
        reductionQuotient_mul_tau u sigma c _
      have hqE : qE * tau (K := K) sigma e = T (K := K) sigma e :=
        reductionQuotient_mul_tau u sigma e _
      calc
        qC * tau (K := K) sigma c = T (K := K) sigma c := hqC
        _ = b * e := hce
        _ = b * T (K := K) sigma e := by rw [hTe]
        _ = b * (qE * tau (K := K) sigma e) := by rw [hqE]
        _ = (b * qE) * tau (K := K) sigma c := by rw [mul_assoc, htaucEq]
  · intro hdiv
    exact dvd_trans hdiv (rho_dvd_T u sigma c)

end HahnSeries.Nonpositive
