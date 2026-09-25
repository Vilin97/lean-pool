/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.NumberTheory.Padics.PadicNumbers
/-!
# The `p`-adic completion used in the global cyclotomic argument

the completion construction constructs localizations using the absolute-value completion
`v.Completion`, whereas the local Kronecker--Weber local cyclotomic theorem is stated
over mathlib's concrete field `ℚ_[p]`.  For the rational `p`-adic absolute
value these are canonically isomorphic.  This file packages that comparison
without adding any hypothesis to the global theorem.
-/

@[expose] public section

noncomputable section

namespace AlgebraicNumberTheory.Valuations


variable (p : ℕ) [Fact p.Prime]

/-- The rational `p`-adic absolute value is nontrivial. -/
theorem padicAbsoluteValue_isNontrivial :
    (Rat.AbsoluteValue.padic p).IsNontrivial := by
  refine ⟨(p : ℚ), by exact_mod_cast (Fact.out : p.Prime).ne_zero, ?_⟩
  apply ne_of_lt
  change ((padicNorm p p : ℚ) : ℝ) < 1
  exact_mod_cast (padicNorm.padicNorm_p_lt_one_of_prime (p := p))

/-- The dense isometric embedding of rational numbers, equipped with their
`p`-adic absolute value, into the concrete field `ℚ_[p]`. -/
noncomputable def padicAbsoluteValueBaseMap :
    WithAbs (Rat.AbsoluteValue.padic p) →+* ℚ_[p] :=
  (Rat.castHom ℚ_[p]).comp
    (WithAbs.equiv (Rat.AbsoluteValue.padic p)).toRingHom

/-- The dense rational embedding preserves the `p`-adic norm. -/
theorem padicAbsoluteValueBaseMap_norm
    (x : WithAbs (Rat.AbsoluteValue.padic p)) :
    ‖padicAbsoluteValueBaseMap p x‖ = ‖x‖ := by
  change ‖((WithAbs.equiv (Rat.AbsoluteValue.padic p) x : ℚ) : ℚ_[p])‖ =
    Rat.AbsoluteValue.padic p (WithAbs.equiv (Rat.AbsoluteValue.padic p) x)
  rw [Padic.eq_padicNorm]
  rfl

/-- The preceding rational embedding is an isometry. -/
theorem padicAbsoluteValueBaseMap_isometry :
    Isometry (padicAbsoluteValueBaseMap p) :=
  AddMonoidHomClass.isometry_of_norm _
    (padicAbsoluteValueBaseMap_norm p)

/-- The canonical ring homomorphism from the absolute-value completion of
`ℚ` at `p` to the concrete `p`-adic field. -/
noncomputable def padicAbsoluteValueCompletionRingHom :
    (Rat.AbsoluteValue.padic p).Completion →+* ℚ_[p] :=
  UniformSpace.Completion.extensionHom
    (padicAbsoluteValueBaseMap p)
    (padicAbsoluteValueBaseMap_isometry p).continuous

/-- On the dense rational subring, the completed map agrees with the original
`p`-adic embedding. -/
@[simp]
theorem padicAbsoluteValueCompletionRingHom_coe
    (x : WithAbs (Rat.AbsoluteValue.padic p)) :
    padicAbsoluteValueCompletionRingHom p
        (x : (Rat.AbsoluteValue.padic p).Completion) =
      padicAbsoluteValueBaseMap p x :=
  UniformSpace.Completion.extensionHom_coe
    (padicAbsoluteValueBaseMap p)
    (padicAbsoluteValueBaseMap_isometry p).continuous x

/-- The completed map remains an isometry. -/
theorem padicAbsoluteValueCompletionRingHom_isometry :
    Isometry (padicAbsoluteValueCompletionRingHom p) :=
  (padicAbsoluteValueBaseMap_isometry p).completion_extension

/-- The completed map is surjective because its closed range contains the
dense copy of `ℚ` in `ℚ_[p]`. -/
theorem padicAbsoluteValueCompletionRingHom_surjective :
    Function.Surjective (padicAbsoluteValueCompletionRingHom p) := by
  let f := padicAbsoluteValueCompletionRingHom p
  have hrangeClosed : IsClosed (Set.range f) :=
    (padicAbsoluteValueCompletionRingHom_isometry p).isClosedEmbedding.isClosed_range
  have hdense : DenseRange ((↑) : ℚ → ℚ_[p]) :=
    Padic.denseRange_ratCast p
  have hrange : Set.range ((↑) : ℚ → ℚ_[p]) ⊆ Set.range f := by
    rintro _ ⟨q, rfl⟩
    let q' : WithAbs (Rat.AbsoluteValue.padic p) :=
      (WithAbs.equiv (Rat.AbsoluteValue.padic p)).symm q
    refine ⟨(q' : (Rat.AbsoluteValue.padic p).Completion), ?_⟩
    change padicAbsoluteValueCompletionRingHom p
        (q' : (Rat.AbsoluteValue.padic p).Completion) = (q : ℚ_[p])
    rw [padicAbsoluteValueCompletionRingHom_coe]
    rfl
  intro x
  have hx : x ∈ closure (Set.range ((↑) : ℚ → ℚ_[p])) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hx

/-- The absolute-value completion of `ℚ` at `p` is the concrete `p`-adic
field. -/
noncomputable def padicAbsoluteValueCompletionRingEquiv :
    (Rat.AbsoluteValue.padic p).Completion ≃+* ℚ_[p] :=
  RingEquiv.ofBijective (padicAbsoluteValueCompletionRingHom p)
    ⟨(padicAbsoluteValueCompletionRingHom_isometry p).injective,
      padicAbsoluteValueCompletionRingHom_surjective p⟩

/-- The same comparison as a `ℚ`-algebra equivalence, in the form needed
to transport the global cyclotomic local extension to the local cyclotomic theorem. -/
noncomputable def padicAbsoluteValueCompletionAlgEquiv :
    (Rat.AbsoluteValue.padic p).Completion ≃ₐ[ℚ] ℚ_[p] where
  __ := padicAbsoluteValueCompletionRingEquiv p
  commutes' q := by
    change padicAbsoluteValueCompletionRingHom p
        (((WithAbs.equiv (Rat.AbsoluteValue.padic p)).symm q :
          WithAbs (Rat.AbsoluteValue.padic p)) :
            (Rat.AbsoluteValue.padic p).Completion) = (q : ℚ_[p])
    rw [padicAbsoluteValueCompletionRingHom_coe]
    rfl

/-- On the dense rational subring, the completion algebra equivalence agrees
with the original `p`-adic embedding. -/
@[simp]
theorem padicAbsoluteValueCompletionAlgEquiv_coe
    (x : WithAbs (Rat.AbsoluteValue.padic p)) :
    padicAbsoluteValueCompletionAlgEquiv p
        (x : (Rat.AbsoluteValue.padic p).Completion) =
      padicAbsoluteValueBaseMap p x :=
  padicAbsoluteValueCompletionRingHom_coe p x

end AlgebraicNumberTheory.Valuations
