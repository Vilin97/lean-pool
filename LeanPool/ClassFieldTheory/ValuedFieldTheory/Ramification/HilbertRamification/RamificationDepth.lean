/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumber
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.UniformizerGradedHom
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.Herbrand.Average
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.AddVal
/-!
# General-DVF ramification numbers as a nonarchimedean depth
-/

@[expose] public section

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher


variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The additive valuation of the target DVR is invariant under the
valuation-ring action supplied by unique extension. -/
theorem addVal_valuationSubringAutOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) (a : target.valuationSubring) :
    IsDiscreteValuationRing.addVal target.valuationSubring
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a) =
      IsDiscreteValuationRing.addVal target.valuationSubring a :=
  IsDiscreteValuationRing.addVal_ringEquiv
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq sigma) a

/-- Product displacement identity for the unique-extension action. -/
theorem valuationSubringAutOfUniqueExtension_mul_sub_eq
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) (sigma tau : Gal(L/K)) :
    valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (sigma * tau) a - a =
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq tau a - a) +
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a) := by
  rw [valuationSubringAutOfUniqueExtension_mul_apply, map_sub]
  ring

/-- States the theorem `ramificationNumberOfUniqueExtension_mul_ge_min`. -/
theorem ramificationNumberOfUniqueExtension_mul_ge_min
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) (sigma tau : Gal(L/K)) :
    min
        (ramificationNumberOfUniqueExtension
          (base := base) (target := target) huniq a sigma)
        (ramificationNumberOfUniqueExtension
          (base := base) (target := target) huniq a tau) ≤
      ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a (sigma * tau) := by
  simp only [ramificationNumberOfUniqueExtension]
  rw [valuationSubringAutOfUniqueExtension_mul_sub_eq
    (base := base) (target := target) huniq]
  rw [← addVal_valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq sigma
    (valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq tau a - a)]
  simpa [min_comm] using
    (IsDiscreteValuationRing.addVal_add
      (R := target.valuationSubring)
      (a := valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq tau a - a))
      (b := valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma a - a))

/-- States the theorem `ramificationNumberOfUniqueExtension_mul_eq_min_of_ne`. -/
theorem ramificationNumberOfUniqueExtension_mul_eq_min_of_ne
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (a : target.valuationSubring) {sigma tau : Gal(L/K)}
    (hne : ramificationNumberOfUniqueExtension
          (base := base) (target := target) huniq a sigma ≠
        ramificationNumberOfUniqueExtension
          (base := base) (target := target) huniq a tau) :
    ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a (sigma * tau) =
      min
        (ramificationNumberOfUniqueExtension
          (base := base) (target := target) huniq a sigma)
        (ramificationNumberOfUniqueExtension
          (base := base) (target := target) huniq a tau) := by
  change IsDiscreteValuationRing.addVal target.valuationSubring
      (valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq (sigma * tau) a - a) = _
  rw [valuationSubringAutOfUniqueExtension_mul_sub_eq
    (base := base) (target := target) huniq]
  have hdistinct :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq tau a - a)) ≠
        IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq sigma a - a) := by
    rw [addVal_valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq]
    exact fun h => hne h.symm
  rw [(IsDiscreteValuationRing.addVal target.valuationSubring).map_add_of_distinct_val
    hdistinct]
  rw [addVal_valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq]
  exact min_comm _ _

/-- States the theorem `ramificationNumberOfUniqueExtension_eq_top_iff`. -/
theorem ramificationNumberOfUniqueExtension_eq_top_iff
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a : target.valuationSubring}
    (ha : Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring) = ⊤)
    (sigma : Gal(L/K)) :
    ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a sigma = ⊤ ↔ sigma = 1 := by
  constructor
  · intro htop
    have hafix : valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq sigma a = a := by
      have hzero : valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma a - a = 0 :=
        (IsDiscreteValuationRing.addVal_eq_top_iff).1 htop
      exact sub_eq_zero.mp hzero
    have hfix : ∀ b : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq sigma b = b := by
      have heq :
          (valuationSubringAlgEquivOfUniqueExtension
            (base := base) (target := target) huniq sigma).toAlgHom =
            AlgHom.id base.valuationSubring target.valuationSubring := by
        apply AlgHom.ext_of_adjoin_eq_top ha
        intro b hb
        simpa only [Set.mem_singleton_iff] using hb ▸ hafix
      intro b
      exact DFunLike.congr_fun heq b
    apply AlgEquiv.ext
    intro y
    let : IsFractionRing target.valuationSubring L :=
      target.valuationSubring_isFractionRing
    obtain ⟨b, c, _hc, hy⟩ :=
      IsFractionRing.div_surjective (A := target.valuationSubring) y
    have hsigmab : sigma (b : L) = (b : L) :=
      congrArg Subtype.val (hfix b)
    have hsigmac : sigma (c : L) = (c : L) :=
      congrArg Subtype.val (hfix c)
    rw [← hy]
    change sigma ((b : L) / (c : L)) = (b : L) / (c : L)
    rw [map_div₀, hsigmab, hsigmac]
  · rintro rfl
    exact ramificationNumberOfUniqueExtension_one
      (base := base) (target := target) huniq a

/-- States the theorem `ramificationNumberOfUniqueExtension_conj`. -/
theorem ramificationNumberOfUniqueExtension_conj
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    {a : target.valuationSubring}
    (ha : Algebra.adjoin base.valuationSubring
      ({a} : Set target.valuationSubring) = ⊤)
    (sigma tau : Gal(L/K)) :
    ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a (tau * sigma * tau⁻¹) =
      ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a sigma := by
  let b := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq tau⁻¹ a
  have hb : Algebra.adjoin base.valuationSubring
      ({b} : Set target.valuationSubring) = ⊤ := by
    change Algebra.adjoin base.valuationSubring
      ({valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq tau⁻¹ a} :
        Set target.valuationSubring) = ⊤
    let e := (valuationSubringAlgEquivOfUniqueExtension
      (base := base) (target := target) huniq tau⁻¹).toAlgHom
    have hmap :
        (Algebra.adjoin base.valuationSubring
          ({a} : Set target.valuationSubring)).map e =
        Algebra.adjoin base.valuationSubring
          ({valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq tau⁻¹ a} :
            Set target.valuationSubring) := by
      simp [e, valuationSubringAlgEquivOfUniqueExtension]
    rw [← hmap, ha, Algebra.map_top]
    change e.range = ⊤
    apply (AlgHom.range_eq_top e).2
    exact (valuationSubringAlgEquivOfUniqueExtension
      (base := base) (target := target) huniq tau⁻¹).surjective
  calc
    ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a (tau * sigma * tau⁻¹) =
        IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq tau
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq sigma b - b)) := by
          simp [ramificationNumberOfUniqueExtension, b,
            valuationSubringAutOfUniqueExtension_mul_apply, map_sub]
    _ = ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq b sigma := by
      rw [addVal_valuationSubringAutOfUniqueExtension]
      rfl
    _ = ramificationNumberOfUniqueExtension
        (base := base) (target := target) huniq a sigma :=
      ramificationNumberOfUniqueExtension_eq_of_adjoin_eq_top
        (base := base) (target := target) huniq hb ha sigma

variable [FiniteDimensional K L] [IsGalois K L]
variable [Algebra.IsSeparable base.residueField target.residueField]

/-- The canonical ramification number is a nonarchimedean depth under
the general DVF standing hypotheses. -/
def ramificationNumberDepthOfUniqueExtension
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target) :
    RamificationTheory.DiscreteValuationField.HerbrandGroupTheory.NonarchimedeanDepth Gal(L/K) where
  depth := intrinsicRamificationNumberOfUniqueExtension
    (base := base) (target := target) huniq
  depth_eq_top_iff := by
    intro sigma
    exact ramificationNumberOfUniqueExtension_eq_top_iff
      (base := base) (target := target) huniq
      (chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
        (base := base) (target := target) huniq) sigma
  depth_mul_ge_min := ramificationNumberOfUniqueExtension_mul_ge_min
    (base := base) (target := target) huniq
      (chosenRamificationGeneratorOfUniqueExtension
        (base := base) (target := target) huniq)
  depth_mul_eq_min_of_ne := ramificationNumberOfUniqueExtension_mul_eq_min_of_ne
    (base := base) (target := target) huniq
      (chosenRamificationGeneratorOfUniqueExtension
        (base := base) (target := target) huniq)
  depth_conj := fun gamma sigma => ramificationNumberOfUniqueExtension_conj
    (base := base) (target := target) huniq
      (chosenRamificationGeneratorOfUniqueExtension_adjoin_eq_top
        (base := base) (target := target) huniq) sigma gamma

/-- States the theorem `ramificationNumberDepthOfUniqueExtension_depth`. -/
@[simp] theorem ramificationNumberDepthOfUniqueExtension_depth
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target)
    (sigma : Gal(L/K)) :
    (ramificationNumberDepthOfUniqueExtension
      (base := base) (target := target) huniq).depth sigma =
      intrinsicRamificationNumberOfUniqueExtension
        (base := base) (target := target) huniq sigma :=
  rfl

end Higher
end RamificationTheory.HilbertRamification
