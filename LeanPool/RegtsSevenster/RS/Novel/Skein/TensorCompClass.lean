/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorInterchange
public import LeanPool.RegtsSevenster.RS.Novel.Skein.HomTensor
public import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinCategory

/-!
# The interchange law on Hom classes

Tensoring two composites is composing the two tensors, descended
to the Hom spaces: the fragment-level interchange at the singles,
extended by the four-fold bilinear induction.
-/

@[expose] public section

namespace RS

variable {R : ℕ} (f : EdgeRankParameter R)

/-- The interchange difference lies in the kernel. -/
theorem mem_ker_interchange {s₁ t₁ u₁ s₂ t₂ u₂ : ℕ}
    (x₁ : Fragment (Fin (s₁ + t₁)) →₀ ℂ)
    (y₁ : Fragment (Fin (t₁ + u₁)) →₀ ℂ)
    (x₂ : Fragment (Fin (s₂ + t₂)) →₀ ℂ)
    (y₂ : Fragment (Fin (t₂ + u₂)) →₀ ℂ) :
    tensorFinsupp s₁ u₁ s₂ u₂
        (composeFinsupp s₁ t₁ u₁ x₁ y₁)
        (composeFinsupp s₂ t₂ u₂ x₂ y₂) -
      composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
        (tensorFinsupp s₁ t₁ s₂ t₂ x₁ x₂)
        (tensorFinsupp t₁ u₁ t₂ u₂ y₁ y₂) ∈
      LinearMap.ker (connectionMap f.val
        ((s₁ + s₂) + (u₁ + u₂))) := by
  -- ═══════ FOUR BILINEAR INDUCTIONS ═══════
  -- The difference is bilinear in each of the four arguments, so
  -- the zero and add branches are formal and the content is at
  -- four single fragments, where it is `tensorComposeInterchange`.
  induction x₁ using Finsupp.induction_linear with
  | zero =>
    simp only [map_zero, LinearMap.zero_apply, sub_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    have he : tensorFinsupp s₁ u₁ s₂ u₂
        (composeFinsupp s₁ t₁ u₁ (a + b) y₁)
        (composeFinsupp s₂ t₂ u₂ x₂ y₂) -
        composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
          (tensorFinsupp s₁ t₁ s₂ t₂ (a + b) x₂)
          (tensorFinsupp t₁ u₁ t₂ u₂ y₁ y₂) =
        (tensorFinsupp s₁ u₁ s₂ u₂
          (composeFinsupp s₁ t₁ u₁ a y₁)
          (composeFinsupp s₂ t₂ u₂ x₂ y₂) -
          composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
            (tensorFinsupp s₁ t₁ s₂ t₂ a x₂)
            (tensorFinsupp t₁ u₁ t₂ u₂ y₁ y₂)) +
        (tensorFinsupp s₁ u₁ s₂ u₂
          (composeFinsupp s₁ t₁ u₁ b y₁)
          (composeFinsupp s₂ t₂ u₂ x₂ y₂) -
          composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
            (tensorFinsupp s₁ t₁ s₂ t₂ b x₂)
            (tensorFinsupp t₁ u₁ t₂ u₂ y₁ y₂)) := by
      simp only [map_add, LinearMap.add_apply]
      abel
    rw [he]
    exact Submodule.add_mem _ ha hb
  | single F₁ c₁ =>
    induction y₁ using Finsupp.induction_linear with
    | zero =>
      simp only [map_zero, LinearMap.zero_apply, sub_zero]
      exact Submodule.zero_mem _
    | add a b ha hb =>
      have he : tensorFinsupp s₁ u₁ s₂ u₂
          (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁)
            (a + b))
          (composeFinsupp s₂ t₂ u₂ x₂ y₂) -
          composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
            (tensorFinsupp s₁ t₁ s₂ t₂
              (Finsupp.single F₁ c₁) x₂)
            (tensorFinsupp t₁ u₁ t₂ u₂ (a + b) y₂) =
          (tensorFinsupp s₁ u₁ s₂ u₂
            (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁) a)
            (composeFinsupp s₂ t₂ u₂ x₂ y₂) -
            composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
              (tensorFinsupp s₁ t₁ s₂ t₂
                (Finsupp.single F₁ c₁) x₂)
              (tensorFinsupp t₁ u₁ t₂ u₂ a y₂)) +
          (tensorFinsupp s₁ u₁ s₂ u₂
            (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁) b)
            (composeFinsupp s₂ t₂ u₂ x₂ y₂) -
            composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
              (tensorFinsupp s₁ t₁ s₂ t₂
                (Finsupp.single F₁ c₁) x₂)
              (tensorFinsupp t₁ u₁ t₂ u₂ b y₂)) := by
        simp only [map_add, LinearMap.add_apply]
        abel
      rw [he]
      exact Submodule.add_mem _ ha hb
    | single G₁ c₁' =>
      induction x₂ using Finsupp.induction_linear with
      | zero =>
        simp only [map_zero, LinearMap.zero_apply, sub_zero]
        exact Submodule.zero_mem _
      | add a b ha hb =>
        have he : tensorFinsupp s₁ u₁ s₂ u₂
            (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁)
              (Finsupp.single G₁ c₁'))
            (composeFinsupp s₂ t₂ u₂ (a + b) y₂) -
            composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
              (tensorFinsupp s₁ t₁ s₂ t₂
                (Finsupp.single F₁ c₁) (a + b))
              (tensorFinsupp t₁ u₁ t₂ u₂
                (Finsupp.single G₁ c₁') y₂) =
            (tensorFinsupp s₁ u₁ s₂ u₂
              (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁)
                (Finsupp.single G₁ c₁'))
              (composeFinsupp s₂ t₂ u₂ a y₂) -
              composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
                (tensorFinsupp s₁ t₁ s₂ t₂
                  (Finsupp.single F₁ c₁) a)
                (tensorFinsupp t₁ u₁ t₂ u₂
                  (Finsupp.single G₁ c₁') y₂)) +
            (tensorFinsupp s₁ u₁ s₂ u₂
              (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁)
                (Finsupp.single G₁ c₁'))
              (composeFinsupp s₂ t₂ u₂ b y₂) -
              composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
                (tensorFinsupp s₁ t₁ s₂ t₂
                  (Finsupp.single F₁ c₁) b)
                (tensorFinsupp t₁ u₁ t₂ u₂
                  (Finsupp.single G₁ c₁') y₂)) := by
          simp only [map_add, LinearMap.add_apply]
          abel
        rw [he]
        exact Submodule.add_mem _ ha hb
      | single F₂ c₂ =>
        induction y₂ using Finsupp.induction_linear with
        | zero =>
          simp only [map_zero, sub_zero]
          exact Submodule.zero_mem _
        | add a b ha hb =>
          have he : tensorFinsupp s₁ u₁ s₂ u₂
              (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁)
                (Finsupp.single G₁ c₁'))
              (composeFinsupp s₂ t₂ u₂ (Finsupp.single F₂ c₂)
                (a + b)) -
              composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
                (tensorFinsupp s₁ t₁ s₂ t₂
                  (Finsupp.single F₁ c₁) (Finsupp.single F₂ c₂))
                (tensorFinsupp t₁ u₁ t₂ u₂
                  (Finsupp.single G₁ c₁') (a + b)) =
              (tensorFinsupp s₁ u₁ s₂ u₂
                (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁)
                  (Finsupp.single G₁ c₁'))
                (composeFinsupp s₂ t₂ u₂
                  (Finsupp.single F₂ c₂) a) -
                composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
                  (tensorFinsupp s₁ t₁ s₂ t₂
                    (Finsupp.single F₁ c₁)
                    (Finsupp.single F₂ c₂))
                  (tensorFinsupp t₁ u₁ t₂ u₂
                    (Finsupp.single G₁ c₁') a)) +
              (tensorFinsupp s₁ u₁ s₂ u₂
                (composeFinsupp s₁ t₁ u₁ (Finsupp.single F₁ c₁)
                  (Finsupp.single G₁ c₁'))
                (composeFinsupp s₂ t₂ u₂
                  (Finsupp.single F₂ c₂) b) -
                composeFinsupp (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
                  (tensorFinsupp s₁ t₁ s₂ t₂
                    (Finsupp.single F₁ c₁)
                    (Finsupp.single F₂ c₂))
                  (tensorFinsupp t₁ u₁ t₂ u₂
                    (Finsupp.single G₁ c₁') b)) := by
            simp only [map_add]
            abel
          rw [he]
          exact Submodule.add_mem _ ha hb
        | single G₂ c₂' =>
          rw [composeFinsupp_single, composeFinsupp_single,
            tensorFinsupp_single, tensorFinsupp_single,
            tensorFinsupp_single, composeFinsupp_single,
            show (c₁ * c₂) * (c₁' * c₂') =
              (c₁ * c₁') * (c₂ * c₂') from by ring]
          exact mem_ker_single_sub_of_equiv_smul f
            (Fragment.tensorComposeInterchange F₁ G₁ F₂ G₂)
            ((c₁ * c₁') * (c₂ * c₂'))

/-- **The interchange law on Hom classes.** -/
theorem HomSpace.tensor_comp {s₁ t₁ u₁ s₂ t₂ u₂ : ℕ}
    (p₁ : HomSpace f.val (s₁ + t₁)) (q₁ : HomSpace f.val (t₁ + u₁))
    (p₂ : HomSpace f.val (s₂ + t₂)) (q₂ : HomSpace f.val (t₂ + u₂)) :
    HomSpace.tensor f s₁ u₁ s₂ u₂
        (HomSpace.comp f s₁ t₁ u₁ p₁ q₁)
        (HomSpace.comp f s₂ t₂ u₂ p₂ q₂) =
      HomSpace.comp f (s₁ + s₂) (t₁ + t₂) (u₁ + u₂)
        (HomSpace.tensor f s₁ t₁ s₂ t₂ p₁ p₂)
        (HomSpace.tensor f t₁ u₁ t₂ u₂ q₁ q₂) := by
  obtain ⟨x₁, rfl⟩ := Submodule.Quotient.mk_surjective _ p₁
  obtain ⟨y₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q₁
  obtain ⟨x₂, rfl⟩ := Submodule.Quotient.mk_surjective _ p₂
  obtain ⟨y₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q₂
  exact (Submodule.Quotient.eq _).mpr
    (mem_ker_interchange f x₁ y₁ x₂ y₂)

end RS
