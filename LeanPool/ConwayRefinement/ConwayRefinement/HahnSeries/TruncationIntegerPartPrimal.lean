/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Negative

/-!
# Primality in a Hahn-series truncation integer part

This module specializes the generic residue-preimage form of LM24, Lemma 9.2.1 to
`Z + L((H^{<0}))`, represented intrinsically as the nonpositive Hahn series whose coefficient at
zero belongs to `Z`. The coefficient-at-zero map is an algebra retraction of constant series.
-/

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {L : Type v}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [Field L]

/-- Nonpositive Hahn series form an algebra over their coefficient field by constant series. -/
instance : Algebra L (Nonpositive G L) where
  algebraMap := C
  smul r x := C r * x
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

/-- The coefficient-field algebra map is the constant-series embedding. -/
@[simp]
theorem algebraMap_apply (r : L) :
    algebraMap L (Nonpositive G L) r = C r := (rfl)

/-- Scalar multiplication commutes with the coercion to Hahn series. -/
@[simp, norm_cast]
theorem coe_smul (r : L) (x : Nonpositive G L) :
    ((r • x : Nonpositive G L) : L⟦G⟧) = r • (x : L⟦G⟧) := by
  rw [Algebra.smul_def, algebraMap_apply, Subring.coe_mul, coe_C,
    HahnSeries.C_mul_eq_smul]

/-- Coefficient at exponent zero as an algebra retraction of the constant-series embedding. -/
def constantCoeffAlgHom : Nonpositive G L →ₐ[L] L where
  __ := constantCoeff
  commutes' r := by
    change constantCoeff (C r : Nonpositive G L) = r
    simp

@[simp]
theorem constantCoeffAlgHom_apply (x : Nonpositive G L) :
    constantCoeffAlgHom x = (x : L⟦G⟧).coeff 0 :=
  constantCoeff_apply x

/-- The truncation integer part is definitionally the residue preimage under coefficient at
zero. -/
theorem truncationIntegerPart_eq_residueSubring (Z : Subring L) :
    truncationIntegerPart G Z =
      Subring.residueSubring (constantCoeffAlgHom (G := G) (L := L)) Z :=
  by
    ext x
    rw [mem_truncationIntegerPart, Subring.mem_residueSubring,
      constantCoeffAlgHom_apply]

/-- The canonical identity-on-elements equivalence with the residue-preimage presentation. -/
def truncationIntegerPartEquivResidueSubring (Z : Subring L) :
    truncationIntegerPart G Z ≃+*
      Subring.residueSubring (constantCoeffAlgHom (G := G) (L := L)) Z where
  toFun x := ⟨x, by rw [← truncationIntegerPart_eq_residueSubring Z]; exact x.2⟩
  invFun x := ⟨x, by rw [truncationIntegerPart_eq_residueSubring Z]; exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- LM24, Lemma 9.2.1 specialized to `Z + L((G^{<0}))`. -/
theorem isPrimal_truncationIntegerPart_iff (Z : Subring L)
    (b : truncationIntegerPart G Z) :
    IsPrimal b ↔
      (constantCoeffAlgHom (b : Nonpositive G L) ≠ 0 ∧
        IsPrimal (⟨constantCoeffAlgHom (b : Nonpositive G L), by
          rw [constantCoeffAlgHom_apply]
          exact (mem_truncationIntegerPart (R := L) (Γ := G)).mp b.2⟩ : Z) ∧
        IsPrimal (b : Nonpositive G L)) ∨
      (constantCoeffAlgHom (b : Nonpositive G L) = 0 ∧
        IsPrimal (⟨(b : Nonpositive G L), Subring.le_fracSubring (by
          change constantCoeffAlgHom (b : Nonpositive G L) ∈ Z
          rw [constantCoeffAlgHom_apply]
          exact (mem_truncationIntegerPart (R := L) (Γ := G)).mp b.2)⟩ :
          Subring.residueSubring constantCoeffAlgHom (Subring.fracSubring Z))) :=
  by
    let e := truncationIntegerPartEquivResidueSubring (G := G) (L := L) Z
    rw [← RingEquiv.isPrimal_iff e b]
    exact Subring.isPrimal_residueSubring_iff (e b).2

/-- At constant coefficient one, primality in the truncation integer part is exactly primality
in the ambient nonpositive Hahn ring. This is the nonzero-residue case used in LM24,
Proposition 9.2.2. -/
theorem isPrimal_truncationIntegerPart_iff_of_constantCoeff_eq_one
    (Z : Subring L) (b : truncationIntegerPart G Z)
    (hb : constantCoeffAlgHom (b : Nonpositive G L) = 1) :
    IsPrimal b ↔ IsPrimal (b : Nonpositive G L) := by
  constructor
  · intro h
    rcases (isPrimal_truncationIntegerPart_iff Z b).mp h with hnonzero | hzero
    · exact hnonzero.2.2
    · exact (one_ne_zero (hb.symm.trans hzero.1)).elim
  · intro h
    apply (isPrimal_truncationIntegerPart_iff Z b).mpr
    left
    refine ⟨?_, ?_, h⟩
    · rw [hb]
      exact one_ne_zero
    · have hone : (⟨constantCoeffAlgHom (b : Nonpositive G L), by
          rw [constantCoeffAlgHom_apply]
          exact (mem_truncationIntegerPart (R := L) (Γ := G)).mp b.2⟩ : Z) = 1 := by
        apply Subtype.ext
        exact hb
      rw [hone]
      intro c d _
      exact ⟨1, 1, one_dvd _, one_dvd _, (mul_one 1).symm⟩

/-- At constant coefficient zero, if the fraction field generated by the coefficient subring is
the whole coefficient field, primality in the truncation integer part is exactly ambient
primality. This is the zero-residue case used in LM24, Proposition 9.2.2. -/
theorem isPrimal_truncationIntegerPart_iff_of_constantCoeff_eq_zero
    (Z : Subring L) (hfrac : Subring.fracSubring Z = ⊤)
    (b : truncationIntegerPart G Z)
    (hb : constantCoeffAlgHom (b : Nonpositive G L) = 0) :
    IsPrimal b ↔ IsPrimal (b : Nonpositive G L) := by
  let e : Subring.residueSubring
        (constantCoeffAlgHom (G := G) (L := L)) (Subring.fracSubring Z) ≃+*
      Nonpositive G L := {
    toFun x := x
    invFun x := ⟨x, by rw [Subring.mem_residueSubring, hfrac]; exact Subring.mem_top _⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl
    map_add' _ _ := rfl }
  constructor
  · intro h
    rcases (isPrimal_truncationIntegerPart_iff Z b).mp h with hnonzero | hzero
    · exact (hnonzero.1 hb).elim
    · let b' : Subring.residueSubring
          (constantCoeffAlgHom (G := G) (L := L)) (Subring.fracSubring Z) :=
          ⟨b, Subring.le_fracSubring (by
            change constantCoeffAlgHom (b : Nonpositive G L) ∈ Z
            rw [constantCoeffAlgHom_apply]
            exact (mem_truncationIntegerPart (R := L) (Γ := G)).mp b.2)⟩
      have hb' : IsPrimal b' := by exact hzero.2
      exact (RingEquiv.isPrimal_iff e b').mpr hb'
  · intro h
    apply (isPrimal_truncationIntegerPart_iff Z b).mpr
    right
    refine ⟨hb, ?_⟩
    let b' : Subring.residueSubring
        (constantCoeffAlgHom (G := G) (L := L)) (Subring.fracSubring Z) :=
        ⟨b, Subring.le_fracSubring (by
          change constantCoeffAlgHom (b : Nonpositive G L) ∈ Z
          rw [constantCoeffAlgHom_apply]
          exact (mem_truncationIntegerPart (R := L) (Γ := G)).mp b.2)⟩
    have hb' := (RingEquiv.isPrimal_iff e b').mp h
    exact hb'

end HahnSeries.Nonpositive
