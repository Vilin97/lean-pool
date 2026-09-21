/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.TruncationDivisibility

/-!
# Primality in a leading-class truncation ring

The fixed points of a closed Archimedean-class truncation form a subring. At the leading class
of a nonzero nonconstant series, every divisor of that series belongs to this subring. Hence the
series is primal in the full nonpositive Hahn ring exactly when it is primal in the fixed-point
subring. This is the source-side localization step in LM24, Proposition 9.2.2.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

/-- Nonpositive Hahn series fixed by closed truncation at `c`. -/
def truncationSubring (c : FiniteArchimedeanClass G) : Subring (Nonpositive G R) :=
  RingHom.range (T (K := K) c)

/-- Membership in the truncation subring is exactly being fixed by the truncation. -/
theorem mem_truncationSubring_iff (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    x ∈ truncationSubring (K := K) (R := R) c ↔ T (K := K) c x = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact T_T c y
  · intro hx
    exact ⟨x, hx⟩

/-- A nonzero nonconstant series, regarded in its leading-class truncation subring. -/
def leadingTruncationElement (b : Nonpositive G R)
    (horder : (b : R⟦G⟧).order ≠ 0) :
    truncationSubring (K := K) (R := R) (leadingClass b horder) :=
  ⟨b, (mem_truncationSubring_iff (leadingClass b horder) b).mpr
    (T_leadingClass b horder)⟩

@[simp]
theorem coe_leadingTruncationElement (b : Nonpositive G R)
    (horder : (b : R⟦G⟧).order ≠ 0) :
    (leadingTruncationElement (K := K) b horder : Nonpositive G R) = b :=
  (rfl)

/-- Primality of a nonzero nonconstant series is unchanged when it is restricted to its
leading-class truncation subring. -/
theorem isPrimal_leadingTruncationElement_iff
    (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) :
    IsPrimal (leadingTruncationElement (K := K) b horder) ↔ IsPrimal b := by
  constructor
  · intro h c d hdvd
    have hdivT : b ∣ T (K := K) (leadingClass b horder) (c * d) :=
      (dvd_iff_dvd_T_leadingClass b hb0 horder (c * d)).mp hdvd
    have hdivLocal : leadingTruncationElement (K := K) b horder ∣
        ⟨T (K := K) (leadingClass b horder) c,
          ⟨c, rfl⟩⟩ *
        ⟨T (K := K) (leadingClass b horder) d,
          ⟨d, rfl⟩⟩ := by
      obtain ⟨q, hq⟩ := hdivT
      have hqFixed : T (K := K) (leadingClass b horder) q = q := by
        apply mul_left_cancel₀ hb0
        calc
          b * T (K := K) (leadingClass b horder) q =
              T (K := K) (leadingClass b horder) b *
                T (K := K) (leadingClass b horder) q := by
                  rw [T_leadingClass b horder]
          _ = T (K := K) (leadingClass b horder) (b * q) := by rw [map_mul]
          _ = T (K := K) (leadingClass b horder)
              (T (K := K) (leadingClass b horder) (c * d)) := by rw [hq]
          _ = T (K := K) (leadingClass b horder) (c * d) := T_T _ _
          _ = b * q := hq
      refine ⟨⟨T (K := K) (leadingClass b horder) q,
        ⟨q, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      change T (K := K) (leadingClass b horder) c *
          T (K := K) (leadingClass b horder) d =
        b * T (K := K) (leadingClass b horder) q
      rw [← map_mul, hq, hqFixed]
    obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h hdivLocal
    refine ⟨(b₁ : Nonpositive G R), (b₂ : Nonpositive G R), ?_, ?_, ?_⟩
    · have hb₁Ne : (b₁ : Nonpositive G R) ≠ 0 := by
        intro hb₁Zero
        have hb₁Zero' : b₁ = 0 := Subtype.ext hb₁Zero
        apply hb0
        have hzero := congrArg Subtype.val hprod
        rw [hb₁Zero', zero_mul] at hzero
        exact hzero
      apply (dvd_iff_dvd_T_of_fixed (leadingClass b horder) b₁.1 hb₁Ne
        ((mem_truncationSubring_iff _ _).mp b₁.2) c).mpr
      exact map_dvd (truncationSubring (K := K) (R := R)
        (leadingClass b horder)).subtype h₁
    · have hb₂Ne : (b₂ : Nonpositive G R) ≠ 0 := by
        intro hb₂Zero
        have hb₂Zero' : b₂ = 0 := Subtype.ext hb₂Zero
        apply hb0
        have hzero := congrArg Subtype.val hprod
        rw [hb₂Zero', mul_zero] at hzero
        exact hzero
      apply (dvd_iff_dvd_T_of_fixed (leadingClass b horder) b₂.1 hb₂Ne
        ((mem_truncationSubring_iff _ _).mp b₂.2) d).mpr
      exact map_dvd (truncationSubring (K := K) (R := R)
        (leadingClass b horder)).subtype h₂
    · exact congrArg Subtype.val hprod
  · intro h c d hdvd
    have hdvdAmbient : b ∣ (c : Nonpositive G R) * (d : Nonpositive G R) :=
      map_dvd (truncationSubring (K := K) (R := R)
        (leadingClass b horder)).subtype hdvd
    obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h hdvdAmbient
    have hb₁Mem : b₁ ∈ truncationSubring (K := K) (R := R) (leadingClass b horder) :=
      (mem_truncationSubring_iff _ _).mpr (T_leadingClass_of_dvd b hb0 horder
        (hprod.symm ▸ dvd_mul_right b₁ b₂))
    have hb₂Mem : b₂ ∈ truncationSubring (K := K) (R := R) (leadingClass b horder) :=
      (mem_truncationSubring_iff _ _).mpr (T_leadingClass_of_dvd b hb0 horder
        (hprod.symm ▸ dvd_mul_left b₂ b₁))
    have hb₁Ne : b₁ ≠ 0 := by
      intro hz
      apply hb0
      rw [hprod, hz, zero_mul]
    have hb₂Ne : b₂ ≠ 0 := by
      intro hz
      apply hb0
      rw [hprod, hz, mul_zero]
    have hq₁Mem : h₁.choose ∈
        truncationSubring (K := K) (R := R) (leadingClass b horder) := by
      apply (mem_truncationSubring_iff _ _).mpr
      apply mul_left_cancel₀ hb₁Ne
      calc
        b₁ * T (K := K) (leadingClass b horder) h₁.choose =
            T (K := K) (leadingClass b horder) (b₁ * h₁.choose) := by
              rw [map_mul, (mem_truncationSubring_iff _ _).mp hb₁Mem]
        _ = T (K := K) (leadingClass b horder) c := by rw [← h₁.choose_spec]
        _ = c := (mem_truncationSubring_iff _ _).mp c.2
        _ = b₁ * h₁.choose := h₁.choose_spec
    have hq₂Mem : h₂.choose ∈
        truncationSubring (K := K) (R := R) (leadingClass b horder) := by
      apply (mem_truncationSubring_iff _ _).mpr
      apply mul_left_cancel₀ hb₂Ne
      calc
        b₂ * T (K := K) (leadingClass b horder) h₂.choose =
            T (K := K) (leadingClass b horder) (b₂ * h₂.choose) := by
              rw [map_mul, (mem_truncationSubring_iff _ _).mp hb₂Mem]
        _ = T (K := K) (leadingClass b horder) d := by rw [← h₂.choose_spec]
        _ = d := (mem_truncationSubring_iff _ _).mp d.2
        _ = b₂ * h₂.choose := h₂.choose_spec
    refine ⟨⟨b₁, hb₁Mem⟩, ⟨b₂, hb₂Mem⟩, ?_, ?_, ?_⟩
    · exact ⟨⟨h₁.choose, hq₁Mem⟩, Subtype.ext h₁.choose_spec⟩
    · exact ⟨⟨h₂.choose, hq₂Mem⟩, Subtype.ext h₂.choose_spec⟩
    · exact Subtype.ext hprod

end HahnSeries.Nonpositive
