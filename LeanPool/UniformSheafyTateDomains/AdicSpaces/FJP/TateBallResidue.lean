/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.RestrictedGaussAdic
import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicNakayama

/-!
# The residue ring of the integral Tate algebra

([hrw-decomposition] "THE TATE LEAF DECOMPOSED", leaf 4, concrete form.)
Through the (4.4) identification `ballAdicEquiv` and the principal adic
quotient `AdicCompletion.quotientSpanEquiv`:

  `E⟨T₁,…,T_m⟩° ⧸ (t) ≃+* E₀[T₁,…,T_m] ⧸ (t)`

for the scaling pseudouniformizer `t` — the restricted coefficients die
modulo `t`, leaving polynomials over the unit ball modulo `t`.
-/

@[expose] public section

open scoped Classical

namespace FiniteJet.GraphKoszul

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E] {m : ℕ}
variable (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1) (ht0 : 0 < ‖t‖)
  (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)

/-- The ball corestriction of the polynomial map (the `gB` of `flat_polyToP`). -/
noncomputable def polyBallRes :
    MvPolynomial (Fin m) ↥(unitBall E) →+* ↥(unitBall (P E m)) :=
  RingHom.codRestrict (polyBall (E := E) (m := m)) (unitBall (P E m))
    (fun q => norm_polyBall_le_one q)

/-- **The (4.4) polynomial compatibility**: `ballAdicEquiv` carries ball
polynomials to their canonical images in the adic completion (extracted from
the inline `hcompat` of `flat_polyToP`). -/
theorem ballAdicEquiv_polyBallRes (q : MvPolynomial (Fin m) ↥(unitBall E)) :
    ballAdicEquiv t htu ht1 ht0 hscale (polyBallRes (E := E) (m := m) q) =
      AdicCompletion.of (I0 (E := E) (m := m) t ht1)
        (MvPolynomial (Fin m) ↥(unitBall E)) q := by
  refine Subtype.ext (funext fun n => ?_)
  show Ideal.Quotient.mk _ (trnc t ht0 n (polyBallRes (E := E) (m := m) q)) = _
  have hval : (AdicCompletion.of (I0 (E := E) (m := m) t ht1)
      (MvPolynomial (Fin m) ↥(unitBall E)) q).val n =
      Ideal.Quotient.mk ((I0 (E := E) (m := m) t ht1) ^ n • ⊤ :
        Ideal (MvPolynomial (Fin m) ↥(unitBall E))) q := rfl
  rw [hval]
  refine mk_trnc_eq t htu ht1 ht0 hscale n (polyBallRes (E := E) (m := m) q) q ?_
  show ‖polyBall q - polyBall q‖ ≤ _
  rw [sub_self, norm_zero]
  exact pow_nonneg (norm_nonneg t) n

/-- The scaling constant as a unit-ball polynomial constant. -/
noncomputable def tConstPoly : MvPolynomial (Fin m) ↥(unitBall E) :=
  MvPolynomial.C (⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ : ↥(unitBall E))

/-- The scaling constant as an element of the integral Tate algebra. -/
noncomputable def tConstBall : ↥(unitBall (P E m)) :=
  polyBallRes (E := E) (m := m) (tConstPoly (E := E) t ht1)

/-- **The residue identification** (leaf 4, concrete): the integral Tate
algebra modulo the scaling constant is the polynomial ring over the unit ball
modulo the constant. -/
noncomputable def unitBallPQuotientEquiv
    (ht_nzd : (tConstPoly (E := E) (m := m) t ht1) ∈
      nonZeroDivisors (MvPolynomial (Fin m) ↥(unitBall E))) :
    (↥(unitBall (P E m)) ⧸
      Ideal.span {tConstBall (E := E) (m := m) t ht1}) ≃+*
    (MvPolynomial (Fin m) ↥(unitBall E) ⧸
      Ideal.span {tConstPoly (E := E) (m := m) t ht1}) := by
  refine RingEquiv.trans
    (Ideal.quotientEquiv
      (Ideal.span {tConstBall (E := E) (m := m) t ht1})
      (Ideal.span {AdicCompletion.of (I0 (E := E) (m := m) t ht1)
        (MvPolynomial (Fin m) ↥(unitBall E))
        (tConstPoly (E := E) (m := m) t ht1)})
      (ballAdicEquiv t htu ht1 ht0 hscale) ?_) ?_
  · -- the span maps to the span of the canonical image
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z})
      (ballAdicEquiv_polyBallRes t htu ht1 ht0 hscale
        (tConstPoly (E := E) (m := m) t ht1)).symm
  · -- the principal adic quotient, aligned at I0 = span {tConstPoly}
    exact AdicCompletion.quotientSpanEquiv ht_nzd

/-- A nonzerodivisor constant is a nonzerodivisor polynomial. -/
theorem C_mem_nonZeroDivisors_mvPolynomial {R : Type*} [CommRing R]
    {σ : Type*} {r : R} (hr : r ∈ nonZeroDivisors R) :
    (MvPolynomial.C r : MvPolynomial σ R) ∈
      nonZeroDivisors (MvPolynomial σ R) := by
  obtain ⟨hrl, -⟩ := mem_nonZeroDivisors_iff.mp hr
  have hcore : ∀ p : MvPolynomial σ R, MvPolynomial.C r * p = 0 → p = 0 := by
    intro p hp
    refine MvPolynomial.ext _ _ fun d => ?_
    have h1 := congrArg (MvPolynomial.coeff d) hp
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_zero] at h1
    rw [MvPolynomial.coeff_zero]
    exact hrl _ h1
  exact mem_nonZeroDivisors_iff.mpr
    ⟨hcore, fun p hp => hcore p (by rwa [mul_comm] at hp)⟩

/-- The scaling unit is a nonzerodivisor of the unit ball. -/
theorem tUnitBall_mem_nonZeroDivisors (htu : IsUnit t) :
    (⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ : ↥(unitBall E)) ∈
      nonZeroDivisors ↥(unitBall E) := by
  have hcore : ∀ x : ↥(unitBall E),
      x * (⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ : ↥(unitBall E)) = 0 →
      x = 0 := by
    intro x hx
    have h1 : (x : E) * t = 0 := congrArg Subtype.val hx
    have h2 : (x : E) = 0 := by
      have h3 := congrArg (· * (↑htu.unit⁻¹ : E)) h1
      simpa [mul_assoc, IsUnit.mul_val_inv] using h3
    exact Subtype.ext h2
  exact mem_nonZeroDivisors_iff.mpr
    ⟨fun x hx => hcore x (by rwa [mul_comm] at hx), hcore⟩

/-- The polynomial scaling constant is a nonzerodivisor. -/
theorem tConstPoly_mem_nonZeroDivisors (htu : IsUnit t) :
    (tConstPoly (E := E) (m := m) t ht1) ∈
      nonZeroDivisors (MvPolynomial (Fin m) ↥(unitBall E)) :=
  C_mem_nonZeroDivisors_mvPolynomial
    (tUnitBall_mem_nonZeroDivisors t ht1 htu)

/-- **The residue ring of the integral Tate algebra is a polynomial ring over
the residue ring of the base** ([hrw-decomposition] Tate leaf 4, final form):
`E⟨T⟩° ⧸ (t) ≃+* (E° ⧸ (t))[T₁,…,T_m]`. -/
noncomputable def unitBallPResidueEquiv :
    (↥(unitBall (P E m)) ⧸
      Ideal.span {tConstBall (E := E) (m := m) t ht1}) ≃+*
    MvPolynomial (Fin m) (↥(unitBall E) ⧸
      Ideal.span {(⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
        ↥(unitBall E))}) :=
  ((unitBallPQuotientEquiv t htu ht1 ht0 hscale
      (tConstPoly_mem_nonZeroDivisors t ht1 htu)).trans
    (Ideal.quotEquivOfEq (show
        Ideal.span {tConstPoly (E := E) (m := m) t ht1} =
        Ideal.map MvPolynomial.C (Ideal.span
          {(⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
            ↥(unitBall E))}) from by
      rw [Ideal.map_span, Set.image_singleton]
      rfl))).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial _).symm.toRingEquiv

/-- Computation law: the quotient identification acts as the identity on
polynomial classes. -/
theorem unitBallPQuotientEquiv_mk
    (ht_nzd : (tConstPoly (E := E) (m := m) t ht1) ∈
      nonZeroDivisors (MvPolynomial (Fin m) ↥(unitBall E)))
    (q : MvPolynomial (Fin m) ↥(unitBall E)) :
    unitBallPQuotientEquiv t htu ht1 ht0 hscale ht_nzd
      (Ideal.Quotient.mk _ (polyBallRes (E := E) (m := m) q)) =
    Ideal.Quotient.mk _ q := by
  show AdicCompletion.quotientSpanEquiv ht_nzd
      ((Ideal.quotientEquiv
        (Ideal.span {tConstBall (E := E) (m := m) t ht1})
        (Ideal.span {AdicCompletion.of (I0 (E := E) (m := m) t ht1)
          (MvPolynomial (Fin m) ↥(unitBall E))
          (tConstPoly (E := E) (m := m) t ht1)})
        (ballAdicEquiv t htu ht1 ht0 hscale)
        (by
          rw [Ideal.map_span, Set.image_singleton]
          exact congrArg (fun z => Ideal.span {z})
            (ballAdicEquiv_polyBallRes t htu ht1 ht0 hscale
              (tConstPoly (E := E) (m := m) t ht1)).symm))
        (Ideal.Quotient.mk _ (polyBallRes (E := E) (m := m) q))) =
    Ideal.Quotient.mk _ q
  rw [Ideal.quotientEquiv_mk, ballAdicEquiv_polyBallRes]
  exact AdicCompletion.quotientSpanEquiv_mk_of ht_nzd q

/-- Computation law: the residue identification sends the class of a constant
to the constant of the class. -/
theorem unitBallPResidueEquiv_mk_C (d : ↥(unitBall E)) :
    unitBallPResidueEquiv t htu ht1 ht0 hscale
      (Ideal.Quotient.mk _ (polyBallRes (E := E) (m := m)
        (MvPolynomial.C d))) =
    MvPolynomial.C (Ideal.Quotient.mk
      (Ideal.span {(⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
        ↥(unitBall E))}) d) := by
  show (MvPolynomial.quotientEquivQuotientMvPolynomial
      (σ := Fin m)
      (Ideal.span {(⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
        ↥(unitBall E))})).symm.toRingEquiv
      ((Ideal.quotEquivOfEq (show
          Ideal.span {tConstPoly (E := E) (m := m) t ht1} =
          Ideal.map MvPolynomial.C (Ideal.span
            {(⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
              ↥(unitBall E))}) from by
        rw [Ideal.map_span, Set.image_singleton]
        rfl))
        ((unitBallPQuotientEquiv t htu ht1 ht0 hscale
          (tConstPoly_mem_nonZeroDivisors t ht1 htu))
          (Ideal.Quotient.mk _ (polyBallRes (E := E) (m := m)
            (MvPolynomial.C d))))) = _
  rw [unitBallPQuotientEquiv_mk, Ideal.quotEquivOfEq_mk]
  show Ideal.Quotient.lift
      (Ideal.map MvPolynomial.C (Ideal.span
        {(⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
          ↥(unitBall E))}) :
        Ideal (MvPolynomial (Fin m) ↥(unitBall E)))
      (MvPolynomial.eval₂Hom
        (MvPolynomial.C.comp (Ideal.Quotient.mk (Ideal.span
          {(⟨t, (mem_unitBall_iff (E := E) t).mpr ht1.le⟩ :
            ↥(unitBall E))}))) MvPolynomial.X)
      (fun _ ha => MvPolynomial.eval₂_C_mk_eq_zero ha)
      (Ideal.Quotient.mk _ (MvPolynomial.C d)) =
    MvPolynomial.C (Ideal.Quotient.mk _ d)
  rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

end FiniteJet.GraphKoszul
