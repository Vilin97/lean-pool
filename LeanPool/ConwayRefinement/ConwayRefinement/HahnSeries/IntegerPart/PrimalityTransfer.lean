/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.IntegerPartSplitting

/-!
# Primality transfer at the leading Archimedean class

This module assembles the generic set-level core of LM24, Proposition 9.2.2. A nonzero
nonconstant element of a Hahn-series truncation integer part is primal exactly when its split
leading truncation is primal in the ambient outer nonpositive Hahn ring, provided the element is
reduced and the embedded inner integer part generates the coefficient Hahn field. The latter is
the exact fraction-field input used in the zero-residue branch of the paper.

The source localization is carried out inside the truncation integer part, not merely inside the
ambient nonpositive Hahn ring. In particular, the quotient constructed when divisibility is
tested after closed-class truncation is proved to retain its coefficient at exponent zero in the
source coefficient subring.
-/

open FiniteArchimedeanClass

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

/-- Closed-class truncation restricted to a truncation integer part. It preserves the
coefficient at exponent zero and hence the coefficient-subring condition. -/
def TIntegerPartRingHom (c : FiniteArchimedeanClass G) (Z : Subring R) :
    truncationIntegerPart G Z →+* truncationIntegerPart G Z where
  toFun x := ⟨T (K := K) c (x : Nonpositive G R), by
    rw [mem_truncationIntegerPart]
    rw [coeff_T_of_mem c (x : Nonpositive G R) (zero_mem _)]
    exact (mem_truncationIntegerPart (R := R) (Γ := G)).mp x.2⟩
  map_one' := Subtype.ext (map_one (T (K := K) c))
  map_mul' x y := Subtype.ext ((T (K := K) c).map_mul
    (x : Nonpositive G R) (y : Nonpositive G R))
  map_zero' := Subtype.ext (map_zero (T (K := K) c))
  map_add' x y := Subtype.ext ((T (K := K) c).map_add
    (x : Nonpositive G R) (y : Nonpositive G R))

/-- The integer-part truncation ring homomorphism agrees with closed-class truncation on the
underlying nonpositive Hahn series. -/
@[simp]
theorem coe_TIntegerPartRingHom (c : FiniteArchimedeanClass G) (Z : Subring R)
    (x : truncationIntegerPart G Z) :
    (TIntegerPartRingHom (K := K) c Z x : Nonpositive G R) =
      T (K := K) c (x : Nonpositive G R) :=
  (rfl)

/-- Divisibility by a nonzero fixed integer-part element can be tested after closed-class
truncation, with the quotient witness remaining in the same integer part. -/
theorem dvd_iff_dvd_TIntegerPart_of_fixed (c : FiniteArchimedeanClass G)
    (Z : Subring R) (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (hbFixed : T (K := K) c (b : Nonpositive G R) = b)
    (x : truncationIntegerPart G Z) :
    b ∣ x ↔ b ∣ TIntegerPartRingHom (K := K) c Z x := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨TIntegerPartRingHom (K := K) c Z q, ?_⟩
    apply Subtype.ext
    change T (K := K) c (x : Nonpositive G R) =
      (b : Nonpositive G R) * T (K := K) c (q : Nonpositive G R)
    rw [show (x : Nonpositive G R) = b * q by exact congrArg Subtype.val hq]
    rw [map_mul, hbFixed]
  · intro h
    have hAmbientT : (b : Nonpositive G R) ∣ T (K := K) c (x : Nonpositive G R) := by
      simpa using map_dvd (truncationIntegerPart G Z).subtype h
    have hAmbient : (b : Nonpositive G R) ∣ (x : Nonpositive G R) :=
      (dvd_iff_dvd_T_of_fixed c (b : Nonpositive G R) hb0 hbFixed x).mpr hAmbientT
    obtain ⟨q, hq⟩ := hAmbient
    obtain ⟨qT, hqT⟩ := h
    have hqTFixed : T (K := K) c q = (qT : Nonpositive G R) := by
      apply mul_left_cancel₀ hb0
      calc
        (b : Nonpositive G R) * T (K := K) c q =
            T (K := K) c b * T (K := K) c q := by rw [hbFixed]
        _ = T (K := K) c ((b : Nonpositive G R) * q) :=
          ((T (K := K) c).map_mul (b : Nonpositive G R) q).symm
        _ = T (K := K) c (x : Nonpositive G R) := by rw [hq]
        _ = (b : Nonpositive G R) * (qT : Nonpositive G R) :=
          congrArg Subtype.val hqT
    let q' : truncationIntegerPart G Z := ⟨q, by
      rw [mem_truncationIntegerPart]
      rw [← coeff_T_of_mem (K := K) c q (zero_mem _), hqTFixed]
      exact (mem_truncationIntegerPart (R := R) (Γ := G)).mp qT.2⟩
    refine ⟨q', ?_⟩
    apply Subtype.ext
    exact hq

/-- A nonconstant integer-part element, regarded in the subring fixed by truncation at its
leading Archimedean class. -/
def leadingFixedIntegerPartElement (Z : Subring R) (b : truncationIntegerPart G Z)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    fixedIntegerPartSubring (K := K) (G := G) (R := R)
      (leadingClass (b : Nonpositive G R) horder) Z :=
  ⟨b, (mem_fixedIntegerPartSubring_iff _ Z b).mpr
    (T_leadingClass (b : Nonpositive G R) horder)⟩

/-- The leading fixed integer-part element has the original integer-part element as its value. -/
@[simp]
theorem coe_leadingFixedIntegerPartElement (Z : Subring R)
    (b : truncationIntegerPart G Z)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    (leadingFixedIntegerPartElement (K := K) Z b horder : truncationIntegerPart G Z) = b :=
  (rfl)

/-- Primality of a nonzero nonconstant integer-part element is unchanged when it is restricted
to the integer-part subring fixed by truncation at its leading class. -/
theorem isPrimal_leadingFixedIntegerPartElement_iff (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    IsPrimal (leadingFixedIntegerPartElement (K := K) Z b horder) ↔ IsPrimal b := by
  let sigma := leadingClass (b : Nonpositive G R) horder
  constructor
  · intro h x y hdvd
    obtain ⟨q, hq⟩ := hdvd
    have hdivLocal : leadingFixedIntegerPartElement (K := K) Z b horder ∣
        ⟨TIntegerPartRingHom (K := K) sigma Z x,
          (mem_fixedIntegerPartSubring_iff sigma Z _).mpr (by
            exact T_T sigma (x : Nonpositive G R))⟩ *
        ⟨TIntegerPartRingHom (K := K) sigma Z y,
          (mem_fixedIntegerPartSubring_iff sigma Z _).mpr (by
            exact T_T sigma (y : Nonpositive G R))⟩ := by
      refine ⟨⟨TIntegerPartRingHom (K := K) sigma Z q,
        (mem_fixedIntegerPartSubring_iff sigma Z _).mpr (by
          exact T_T sigma (q : Nonpositive G R))⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change T (K := K) sigma (x : Nonpositive G R) * T (K := K) sigma y =
        (b : Nonpositive G R) * T (K := K) sigma q
      rw [← map_mul]
      rw [show (x : Nonpositive G R) * y = b * q by exact congrArg Subtype.val hq]
      rw [map_mul, T_leadingClass (b : Nonpositive G R) horder]
    obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h hdivLocal
    have hprodSource : b = (b₁ : truncationIntegerPart G Z) * b₂ := by
      simpa using congrArg Subtype.val hprod
    have hb₁Ne : (b₁ : Nonpositive G R) ≠ 0 := by
      intro hz
      apply hb0
      rw [show (b : Nonpositive G R) = b₁ * b₂ by
        exact congrArg Subtype.val hprodSource]
      rw [hz, zero_mul]
    have hb₂Ne : (b₂ : Nonpositive G R) ≠ 0 := by
      intro hz
      apply hb0
      rw [show (b : Nonpositive G R) = b₁ * b₂ by
        exact congrArg Subtype.val hprodSource]
      rw [hz, mul_zero]
    refine ⟨(b₁ : truncationIntegerPart G Z), (b₂ : truncationIntegerPart G Z), ?_, ?_, ?_⟩
    · refine (dvd_iff_dvd_TIntegerPart_of_fixed (K := K) (R := R) sigma Z b₁ hb₁Ne
        ((mem_fixedIntegerPartSubring_iff sigma Z _).mp b₁.2) x).mpr ?_
      exact map_dvd
        (fixedIntegerPartSubring (K := K) (G := G) (R := R) sigma Z).subtype h₁
    · refine (dvd_iff_dvd_TIntegerPart_of_fixed (K := K) (R := R) sigma Z b₂ hb₂Ne
        ((mem_fixedIntegerPartSubring_iff sigma Z _).mp b₂.2) y).mpr ?_
      exact map_dvd
        (fixedIntegerPartSubring (K := K) (G := G) (R := R) sigma Z).subtype h₂
    · exact hprodSource
  · intro h x y hdvd
    have hdvdSource : b ∣ (x : truncationIntegerPart G Z) *
        (y : truncationIntegerPart G Z) :=
      map_dvd (fixedIntegerPartSubring (K := K) (G := G) (R := R) sigma Z).subtype hdvd
    obtain ⟨b₁, b₂, h₁, h₂, hprod⟩ := h hdvdSource
    have hb₁Mem : T (K := K) sigma (b₁ : Nonpositive G R) = b₁ := by
      apply T_leadingClass_of_dvd (b : Nonpositive G R) hb0 horder
      exact map_dvd (truncationIntegerPart G Z).subtype
        (hprod.symm ▸ dvd_mul_right b₁ b₂)
    have hb₂Mem : T (K := K) sigma (b₂ : Nonpositive G R) = b₂ := by
      apply T_leadingClass_of_dvd (b : Nonpositive G R) hb0 horder
      exact map_dvd (truncationIntegerPart G Z).subtype
        (hprod.symm ▸ dvd_mul_left b₂ b₁)
    have hb₁Ne : (b₁ : Nonpositive G R) ≠ 0 := by
      intro hz
      apply hb0
      rw [show (b : Nonpositive G R) = b₁ * b₂ by exact congrArg Subtype.val hprod]
      rw [hz, zero_mul]
    have hb₂Ne : (b₂ : Nonpositive G R) ≠ 0 := by
      intro hz
      apply hb0
      rw [show (b : Nonpositive G R) = b₁ * b₂ by exact congrArg Subtype.val hprod]
      rw [hz, mul_zero]
    have hq₁Mem : T (K := K) sigma (h₁.choose : Nonpositive G R) = h₁.choose := by
      apply mul_left_cancel₀ hb₁Ne
      calc
        (b₁ : Nonpositive G R) * T (K := K) sigma h₁.choose =
            T (K := K) sigma b₁ * T (K := K) sigma h₁.choose := by rw [hb₁Mem]
        _ = T (K := K) sigma
            ((b₁ : Nonpositive G R) * (h₁.choose : Nonpositive G R)) :=
          ((T (K := K) sigma).map_mul (b₁ : Nonpositive G R)
            (h₁.choose : Nonpositive G R)).symm
        _ = T (K := K) sigma (x : Nonpositive G R) := by
          rw [← show (x : Nonpositive G R) =
            (b₁ : Nonpositive G R) * (h₁.choose : Nonpositive G R) by
              exact congrArg Subtype.val h₁.choose_spec]
        _ = (x : Nonpositive G R) := (mem_fixedIntegerPartSubring_iff sigma Z _).mp x.2
        _ = (b₁ : Nonpositive G R) * (h₁.choose : Nonpositive G R) :=
          congrArg Subtype.val h₁.choose_spec
    have hq₂Mem : T (K := K) sigma (h₂.choose : Nonpositive G R) = h₂.choose := by
      apply mul_left_cancel₀ hb₂Ne
      calc
        (b₂ : Nonpositive G R) * T (K := K) sigma h₂.choose =
            T (K := K) sigma b₂ * T (K := K) sigma h₂.choose := by rw [hb₂Mem]
        _ = T (K := K) sigma
            ((b₂ : Nonpositive G R) * (h₂.choose : Nonpositive G R)) :=
          ((T (K := K) sigma).map_mul (b₂ : Nonpositive G R)
            (h₂.choose : Nonpositive G R)).symm
        _ = T (K := K) sigma (y : Nonpositive G R) := by
          rw [← show (y : Nonpositive G R) =
            (b₂ : Nonpositive G R) * (h₂.choose : Nonpositive G R) by
              exact congrArg Subtype.val h₂.choose_spec]
        _ = (y : Nonpositive G R) := (mem_fixedIntegerPartSubring_iff sigma Z _).mp y.2
        _ = (b₂ : Nonpositive G R) * (h₂.choose : Nonpositive G R) :=
          congrArg Subtype.val h₂.choose_spec
    refine ⟨⟨b₁, (mem_fixedIntegerPartSubring_iff sigma Z _).mpr hb₁Mem⟩,
      ⟨b₂, (mem_fixedIntegerPartSubring_iff sigma Z _).mpr hb₂Mem⟩, ?_, ?_, ?_⟩
    · exact ⟨⟨h₁.choose, (mem_fixedIntegerPartSubring_iff sigma Z _).mpr hq₁Mem⟩,
        Subtype.ext h₁.choose_spec⟩
    · exact ⟨⟨h₂.choose, (mem_fixedIntegerPartSubring_iff sigma Z _).mpr hq₂Mem⟩,
        Subtype.ext h₂.choose_spec⟩
    · exact Subtype.ext hprod

/-- Splitting the leading fixed integer-part element gives its split truncation in the exact
embedded inner integer part. -/
theorem splitFixedIntegerPartRingEquiv_leadingFixedIntegerPartElement
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0) :
    splitFixedIntegerPartRingEquiv u (leadingClass (b : Nonpositive G R) horder) Z
        (leadingFixedIntegerPartElement (K := K) Z b horder) =
      splitTruncationIntegerPart u (leadingClass (b : Nonpositive G R) horder)
        (innerIntegerPartSubring (K := K) (G := G)
          (leadingClass (b : Nonpositive G R) horder) Z)
        (b : Nonpositive G R)
        (tauBall_mem_innerIntegerPartSubring
          (leadingClass (b : Nonpositive G R) horder) Z b) := by
  apply Subtype.ext
  rw [coe_splitFixedIntegerPartRingEquiv, coe_splitTruncationIntegerPart]
  rw [show (leadingFixedIntegerPartElement (K := K) Z b horder :
    truncationIntegerPart G Z) = b from coe_leadingFixedIntegerPartElement Z b horder]

/-- In the residue-one branch, source primality is equivalent to ambient primality of the split
truncation without any fraction-field hypothesis. -/
theorem isPrimal_iff_isPrimal_splitTruncation_of_tau_eq_one
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (htau : tauBall (K := K) (leadingClass (b : Nonpositive G R) horder)
      (b : Nonpositive G R) = 1) :
    IsPrimal b ↔
      IsPrimal (splitTruncation u (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R)) := by
  let sigma := leadingClass (b : Nonpositive G R) horder
  let bFixed := leadingFixedIntegerPartElement (K := K) Z b horder
  let e := splitFixedIntegerPartRingEquiv u sigma Z
  let S := innerIntegerPartSubring (K := K) (G := G) sigma Z
  calc
    IsPrimal b ↔ IsPrimal bFixed :=
      (isPrimal_leadingFixedIntegerPartElement_iff (K := K) Z b hb0 horder).symm
    _ ↔ IsPrimal (e bFixed) := (RingEquiv.isPrimal_iff e bFixed).symm
    _ ↔ IsPrimal (splitTruncationIntegerPart u sigma S (b : Nonpositive G R)
        (htau.symm ▸ S.one_mem)) := by
      rw [show e bFixed = splitTruncationIntegerPart u sigma S (b : Nonpositive G R)
          (tauBall_mem_innerIntegerPartSubring sigma Z b) by
        exact splitFixedIntegerPartRingEquiv_leadingFixedIntegerPartElement u Z b horder]
    _ ↔ IsPrimal (splitTruncation u sigma (b : Nonpositive G R)) :=
      isPrimal_splitTruncationIntegerPart_iff_of_tau_eq_one u sigma S
        (b : Nonpositive G R) htau

/-- In the residue-zero branch, source primality is equivalent to ambient primality of the split
truncation when the embedded inner integer part generates the coefficient Hahn field. -/
theorem isPrimal_iff_isPrimal_splitTruncation_of_tau_eq_zero
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hfrac : Subring.fracSubring
      (innerIntegerPartSubring (K := K) (G := G)
        (leadingClass (b : Nonpositive G R) horder) Z) = ⊤)
    (htau : tauBall (K := K) (leadingClass (b : Nonpositive G R) horder)
      (b : Nonpositive G R) = 0) :
    IsPrimal b ↔
      IsPrimal (splitTruncation u (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R)) := by
  let sigma := leadingClass (b : Nonpositive G R) horder
  let bFixed := leadingFixedIntegerPartElement (K := K) Z b horder
  let e := splitFixedIntegerPartRingEquiv u sigma Z
  let S := innerIntegerPartSubring (K := K) (G := G) sigma Z
  calc
    IsPrimal b ↔ IsPrimal bFixed :=
      (isPrimal_leadingFixedIntegerPartElement_iff (K := K) Z b hb0 horder).symm
    _ ↔ IsPrimal (e bFixed) := (RingEquiv.isPrimal_iff e bFixed).symm
    _ ↔ IsPrimal (splitTruncationIntegerPart u sigma S (b : Nonpositive G R)
        (htau.symm ▸ S.zero_mem)) := by
      rw [show e bFixed = splitTruncationIntegerPart u sigma S (b : Nonpositive G R)
          (tauBall_mem_innerIntegerPartSubring sigma Z b) by
        exact splitFixedIntegerPartRingEquiv_leadingFixedIntegerPartElement u Z b horder]
    _ ↔ IsPrimal (splitTruncation u sigma (b : Nonpositive G R)) :=
      isPrimal_splitTruncationIntegerPart_iff_of_tau_eq_zero u sigma S hfrac
        (b : Nonpositive G R) htau

/-- Set-level primality transfer from LM24, Proposition 9.2.2. Generation of the coefficient Hahn
field by the embedded inner integer part is required only when the leading residue is zero. -/
theorem isPrimal_iff_isPrimal_splitTruncation_of_isReduced
    (u : HahnEmbedding.ArchimedeanStrata K G) (Z : Subring R)
    (b : truncationIntegerPart G Z) (hb0 : (b : Nonpositive G R) ≠ 0)
    (horder : ((b : Nonpositive G R) : R⟦G⟧).order ≠ 0)
    (hbReduced : IsReduced (b : Nonpositive G R))
    (hfrac : tauBall (K := K) (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R) = 0 →
      Subring.fracSubring (innerIntegerPartSubring (K := K) (G := G)
        (leadingClass (b : Nonpositive G R) horder) Z) = ⊤) :
    IsPrimal b ↔
      IsPrimal (splitTruncation u (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R)) := by
  rcases (isReduced_iff_tau_leadingClass_eq_zero_or_one (K := K)
    (b : Nonpositive G R) hb0 horder).mp hbReduced with htau | htau
  · have htauBall : tauBall (K := K) (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R) = 0 :=
      (tauBall_eq_zero_iff (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R)).mpr htau
    exact isPrimal_iff_isPrimal_splitTruncation_of_tau_eq_zero u Z b hb0 horder
      (hfrac htauBall) htauBall
  · have htauBall : tauBall (K := K) (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R) = 1 := by
      exact tauBall_eq_one_of_tau_eq_one (leadingClass (b : Nonpositive G R) horder)
        (b : Nonpositive G R) htau
    exact isPrimal_iff_isPrimal_splitTruncation_of_tau_eq_one u Z b hb0 horder htauBall

end HahnSeries.Nonpositive
