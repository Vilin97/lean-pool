/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic


/-!
# ClassifyInterval

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

namespace OneMfld

open Function
open Set

theorem ici_cap_iio_empty (y : Real) : (Ici y ∩ Iio y) = ∅ := by
    have h' : Ici y ∩ Iio y = Ico y y := rfl
    rw [h']
    simp only [lt_self_iff_false, not_false_eq_true, Ico_eq_empty]

theorem iic_cap_ioi_empty (y : Real) : (Iic y ∩ Ioi y) = ∅ := by
    have h' : Iic y ∩ Ioi y = Ioc y y := Iic_inter_Ioi
    rw [h']
    simp only [lt_self_iff_false, not_false_eq_true, Ioc_eq_empty]

theorem not_ici (U : Set Real) (y : Real) (hu : IsOpen U) : (Ici y ≠ U) := by
  by_contra h
  rw [←h] at hu
  have h''' : IsClosed (Ici y) := by
      apply isClosed_Ici
  have ho : IsOpen (Ici y)ᶜ
  · exact IsClosed.isOpen_compl
  have hr : IsPreconnected (univ : Set Real) := isPreconnected_univ
  let hr' := hr (Ici y) ((Ici y)ᶜ) hu ho
  have huniv : Ici y ∪ (Ici y)ᶜ = univ := union_compl_self (Ici y)
  rw [huniv] at hr'
  simp only [subset_refl, univ_inter, nonempty_Ici, compl_Ici, nonempty_Iio, forall_const] at hr'
  rw [ici_cap_iio_empty] at hr'
  apply Set.not_nonempty_empty
  exact hr'

theorem not_iic (U : Set Real) (y : Real) (hu : IsOpen U) : (Iic y ≠ U) := by
  by_contra h
  rw [←h] at hu
  have h''' : IsClosed (Iic y) := by
      apply isClosed_Iic
  have ho : IsOpen (Iic y)ᶜ
  · exact IsClosed.isOpen_compl
  have hr : IsPreconnected (univ : Set Real) := isPreconnected_univ
  let hr' := hr (Iic y) ((Iic y)ᶜ) hu ho
  have huniv : Iic y ∪ (Iic y)ᶜ = univ := union_compl_self (Iic y)
  rw [huniv] at hr'
  simp only [subset_refl, univ_inter, nonempty_Iic, compl_Iic, nonempty_Ioi, forall_const] at hr'
  rw [iic_cap_ioi_empty] at hr'
  apply Set.not_nonempty_empty
  exact hr'

lemma ioc_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Ioc x y) := by
  have hu : (Ioc x y) ∪ (Iio y) = (Iic y)
  · ext p
    simp only [mem_union, mem_Ioc, mem_Iio, mem_Iic]
    apply Iff.intro
    · intro h
      rcases h with (h1|h2)
      · tauto
      · exact le_of_lt h2
    by_cases hp : p = y
    · intro h
      rw [hp]
      simp only [le_refl, and_true, lt_self_iff_false, or_false]
      exact hxy
    intro h
    right
    exact lt_of_le_of_ne h hp
  by_contra hopen
  have hopen' : IsOpen (Iio y) := isOpen_Iio
  have hopen'' : IsOpen (Iic y)
  · rw [←hu]
    exact IsOpen.union hopen hopen'
  have hc : IsOpen ((Iic y)ᶜ)
  · simp only [compl_Iic]
    exact isOpen_Ioi
  have hcon := isPreconnected_univ (Iic y) ((Iic y)ᶜ) hopen'' hc
               (by simp only [compl_Iic, Iic_union_Ioi, subset_refl])
               (by simp only [univ_inter, nonempty_Iic])
               (by simp only [compl_Iic, univ_inter, nonempty_Ioi])
  simp only [compl_Iic, univ_inter] at hcon
  rcases hcon with ⟨x,hx⟩
  simp at hx
  linarith

lemma ico_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Ico x y) := by
  have hxy' : -y < -x := neg_lt_neg_iff.mpr hxy
  have hn := ioc_not_open (-y) (-x) hxy'
  let f : Real → Real := fun x => - x
  let fb : Bijective f := ⟨ neg_injective, neg_surjective ⟩
  let fe := Equiv.ofBijective f fb
  have fc : Continuous fe := continuous_neg
  have fo : IsOpenMap fe := isOpenMap_neg ℝ
  have fh : Homeomorph Real Real
  · apply Equiv.toHomeomorphOfContinuousOpen
    · exact fc
    exact fo
  by_contra h
  have p := fo (Ico x y) h
  have he : fe '' (Ico x y) = Ioc (-y) (-x)
  · ext t
    have ht : ∀ s : Real, fe.symm (-s) = s := fun s => Equiv.ofBijective_symm_apply_apply f fb s
    have ht' := ht (-t)
    simp only [neg_neg] at ht'
    simp only [mem_image_equiv, mem_Ico, mem_Ioc]
    apply Iff.intro
    · simp only [and_imp]
      intro h1 h2
      constructor
      · rw [ht'] at h1
        rw [ht'] at h2
        linarith
      rw [ht'] at h1
      rw [ht'] at h2
      linarith
    simp only [and_imp]
    intro h1 h2
    rw [ht']
    constructor
    · linarith
    linarith
  · rw [he] at p
    exact hn p

lemma icc_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Icc x y) := by
  by_contra h
  have hc : IsClosed (Icc x y) := isClosed_Icc
  have hc'' : IsOpen ((Icc x y)ᶜ) := IsClosed.isOpen_compl
  have hcon := isPreconnected_univ (Icc x y) ((Icc x y)ᶜ) h hc''
               (by simp only [union_compl_self, subset_refl])
               (by simp only [univ_inter, nonempty_Icc]
                   linarith)
               (by simp only [univ_inter]
                   have hy : ((y + 1) ∈ (Icc x y)ᶜ)
                   · simp only [mem_compl_iff, mem_Icc, add_le_iff_nonpos_right, not_and, not_le,
                       zero_lt_one, implies_true]
                   exact nonempty_of_mem hy)
  simp only [inter_compl_self, inter_empty, Set.not_nonempty_empty] at hcon

lemma not_ioc (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Ioc x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Ioc x y)
    · apply ioc_not_open x y
      exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · have h' : Ioc x y = ∅
    · exact Ioc_eq_empty hxy
    rw [h] at h'
    tauto

theorem not_ico (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Ico x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Ico x y)
    · apply ico_not_open x y
      exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · have h' : Ico x y = ∅
    · exact Ico_eq_empty hxy
    rw [h] at h'
    tauto

theorem not_icc (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Icc x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Icc x y)
    · apply icc_not_open x y
      exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · by_cases hyx : (x > y)
    · have h' : Icc x y = ∅
      · exact Icc_eq_empty_of_lt hyx
      rw [h] at h'
      exact h'
    · have hxy' : x ≥ y := le_of_not_gt hxy
      have hyx' : x ≤ y := by exact le_of_not_gt hyx
      have hxx : x = y
      · have hxy'' : (x = y) ∨ (y < x) := eq_or_gt_of_not_lt hxy
        have hyx'' : (x = y) ∨ (x < y) := by exact Or.symm (Decidable.lt_or_eq_of_le hyx')
        rcases hyx'' with (h|h)
        · exact h
        tauto
      rw [←hxx] at h
      simp only [Icc_self] at h
      rw [←h] at hu
      exfalso
      have c : ¬ IsOpen {x} := not_isOpen_singleton x
      tauto

theorem classify_intervals (U : Set Real) (hu : IsOpen U) (hc : IsPreconnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : Real), (U = Set.Iio x)) ∨
  (∃ (x : Real), (Set.Ioi x = U)) ∨
  (U = univ) ∨ (U = ∅) := by
  have h : U ∈ (range (uncurry Icc)) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range
      (uncurry Ioo) ∪  (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅})
  · rw [←setOfPred_isPreconnected_eq_of_ordered]
    exact hc
  simp only [union_insert, union_singleton, mem_insert_iff, mem_union, mem_range, Prod.exists,
    uncurry_apply_pair] at h
  cases h
  case inl h => tauto
  case inr h =>
    cases h
    case inl h => tauto
    case inr h =>
      cases h
      case inr h =>
        cases h
        case inl h =>
          cases h
          case inr h => by_contra
                        rcases h with ⟨ x', hx ⟩
                        apply not_iic
                        · exact hu
                        exact hx
          case inl h =>
            cases h
            case inr h => right; right; left; assumption
            case inl h => by_contra
                          rcases h with ⟨ x', hx ⟩
                          apply not_ici
                          · exact hu
                          exact hx
        case inr h => tauto
      case inl h =>
        cases h
        case inr h => left; tauto
        case inl h =>
          cases h
          case inl h =>
            cases h
            case inl h => rcases h with ⟨ x, y, hx ⟩
                          right; right; right; right
                          apply not_icc
                          · exact hu
                          exact hx
            case inr h => rcases h with ⟨ x, y, hx ⟩
                          right; right; right; right
                          apply not_ico
                          · exact hu
                          exact hx
          case inr h => rcases h with ⟨ x, y, hx ⟩
                        right
                        right
                        right
                        right
                        apply not_ioc
                        · exact hu
                        exact hx

/-- Select disjuncts repeatedly to reduce a nested disjunction to one of its branches. -/
macro "solveDisj" : tactic => `(tactic| repeat (apply Or.inl <|> apply Or.inr))

theorem classify_connected_interval (U : Set Real) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : Real), (U = Set.Iio x)) ∨
  (∃ (x : Real), (Set.Ioi x = U)) ∨
  (U = univ) := by
    have hpc : IsPreconnected U := by exact IsConnected.isPreconnected hc
    have hi := classify_intervals U hu hpc
    have ho : ¬ (U = ∅) := by
      by_contra hn
      rw [hn] at hc
      have he : (∅ : Set Real).Nonempty := IsConnected.nonempty hc
      exact Set.not_nonempty_empty he
    rcases hi with (h|h|h|h|h)
    · left; assumption
    · right; left; assumption
    · right; right; left; assumption
    · right; right; right; assumption
    exfalso
    exact ho h

/-- The logarithm homeomorphism from positive nonnegative reals to the real line. -/
noncomputable def homeoNnrealReal : (Set.Ioi 0 : Set NNReal) ≃ₜ (Set.univ : Set Real) where
  toFun := fun ⟨x,_⟩ => ⟨ Real.log x, trivial ⟩
  invFun := fun ⟨x,_⟩ => ⟨ NNReal.mk (Real.exp x) (Real.exp_nonneg x), Real.exp_pos x ⟩
  left_inv := fun ⟨ ⟨ x, nn ⟩, p ⟩  => by
    ext
    simp only [NNReal.coe_mk]
    exact Real.exp_log p
  right_inv := fun x => by
    simp only [NNReal.coe_mk, Real.log_exp, Subtype.coe_eta]
  continuous_toFun := by
    simp only
    refine Continuous.subtype_mk ?_ fun x => trivial
    refine Continuous.log ?_ ?_
    · exact Isometry.continuous fun x1 => congrFun rfl
    intro x
    rcases x with ⟨x,hx⟩
    simp only [ne_eq, NNReal.coe_eq_zero]
    exact pos_iff_ne_zero.mp hx
  continuous_invFun := by
    simp only
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.rexp
    exact continuous_subtype_val

/-- Truncate a real number at zero and regard the result as a nonnegative real. -/
def relu (x : ℝ) : NNReal :=
  NNReal.mk (max x 0) (by simp)

lemma relu_zero : (relu 0 = 0) := by
  have : max (0 : Real) (0 : Real) = (0 : Real) := by exact max_self 0
  dsimp [relu]
  simp only [max_self, NNReal.mk_zero]

theorem continuous_relu : Continuous relu := by
  apply Continuous.subtype_mk
  apply Continuous.max
  · exact continuous_id'
  exact continuous_const


lemma proj_relu {x : ℝ} (h : x > 0) : (relu x).toReal = x := by
  have : max x 0 = x := max_eq_left_of_lt h
  exact this

lemma proj_relu' {x : ℝ} (h : x <= 0) : (relu x).toReal = 0 := by
  have : 0 = max x 0 := right_eq_sup.mpr h
  dsimp [relu]
  rw [←this]

lemma relu_proj {x : NNReal} : (relu x.toReal) = x := by
  by_cases h0 : x = 0
  · rw [h0]
    simp only [NNReal.coe_zero]
    rw [relu_zero]
  · have : x > 0 := by exact pos_iff_ne_zero.mpr h0
    refine NNReal.eq ?_
    rw [proj_relu]
    exact this

lemma relu_mono : StrictMonoOn relu (Set.Ici 0) := by
  intro x hx y hy h
  simp only [mem_Ici] at hx
  simp only [mem_Ici] at hy
  apply NNReal.coe_lt_coe.mp
  by_cases hx0 : x = 0
  · rw [hx0]
    simp only [NNReal.coe_lt_coe]
    by_cases hy0 : y = 0
    · rw [hy0]
      simp only [lt_self_iff_false]
      linarith
    · have hy' : y > 0 := by linarith
      apply NNReal.coe_lt_coe.mp
      rw [proj_relu hy']
      rw [relu_zero]
      simp only [NNReal.coe_zero]
      assumption
  · have hx' : x > 0 := by exact lt_of_le_of_ne hx fun a => hx0 (id (Eq.symm a))
    rw [proj_relu hx']
    by_cases hy0 : y = 0
    · rw [hy0]
      rw [relu_zero]
      simp only [NNReal.coe_zero, gt_iff_lt]
      linarith
    · have hy' : y > 0 := by linarith
      rw [proj_relu hy']
      assumption

lemma relu_interval_ioo {U : Set NNReal} {a b : Real} (h : Ioo a b = relu ⁻¹' U) :
  (relu '' (Set.Ioo a b) = U) := by
  apply subset_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [h] at hy
    exact hy
  · intro x hx
    refine ⟨(x : ℝ), ?_, relu_proj⟩
    rw [h]
    simpa only [mem_preimage, relu_proj] using hx

theorem StrictMonoOn.injOn_Ioo {α : Type u_1} {β : Type u_2} {f : α → β}
  [LinearOrder α] [LinearOrder β] {a : α} {b : α} (h : StrictMonoOn f (Set.Icc a b)) :
  InjOn f (Set.Ioo a b) := by
  exact (h.mono Ioo_subset_Icc_self).injOn

lemma relu_ioo (a b : Real) :
  (relu '' (Set.Ioo a b) = Set.Ioo (relu a) (relu b)) ∨
  (relu '' (Set.Ioo a b) = Set.Ico 0 (relu b)) ∨
  (relu '' (Set.Ioo a b) = { 0 }) ∨
  (relu '' (Set.Ioo a b) = ∅) := by
  by_cases ha : a > 0
  · by_cases hb : b > 0
    · left
      ext z
      simp only [mem_image, mem_Ioo]
      constructor
      · intro ⟨ x, ⟨ hx, hxz ⟩ ⟩
        have hax : relu a < relu x := by
          apply NNReal.coe_lt_coe.mp
          rw [proj_relu]
          · rw [proj_relu]
            · exact hx.1
            linarith
          linarith
        have hxb : relu x < relu b := by
          apply NNReal.coe_lt_coe.mp
          rw [proj_relu]
          · rw [proj_relu]
            · exact hx.2
            linarith
          linarith
        rw [hxz] at hax
        rw [hxz] at hxb
        exact ⟨hax, hxb⟩
      · intro ⟨ haz, hzb ⟩
        use z
        rw [relu_proj]
        simp only [and_true]
        have haz' : NNReal.toReal (relu a) < NNReal.toReal z := by exact haz
        have hzb' : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
        rw [proj_relu] at hzb'
        · rw [proj_relu] at haz'
          · exact ⟨haz', hzb'⟩
          exact ha
        exact hb
    · have : Ioo a b = ∅ := by
        ext z
        simp only [mem_Ioo, mem_empty_iff_false, iff_false, not_and, not_lt]
        intro ha
        linarith
      rw [this]
      simp only [image_empty]
      simp only [or_true]
  · by_cases hb : b > 0
    · by_cases ha0 : a = 0
      · rw [ha0]
        left
        ext z
        simp only [mem_image, mem_Ioo]
        apply Iff.intro
        · intro ⟨ y, ⟨ h0y, hyb ⟩, hyz ⟩
          rw [←hyz]
          apply And.intro
          · rw [relu_zero]
            have : 0 < NNReal.toReal (relu y) := by
              rw [proj_relu]
              · assumption
              linarith
            simp only [gt_iff_lt]
            exact this
          · have : NNReal.toReal (relu y) < NNReal.toReal (relu b) := by
              rw [proj_relu]
              · rw [proj_relu]
                · assumption
                linarith
              linarith
            exact this
        · intro ⟨ h0z, hzb ⟩
          use z.toReal
          apply And.intro
          · apply And.intro
            · simp only [NNReal.coe_pos]
              exact pos_of_gt h0z
            · have : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
              exact Real.lt_toNNReal_iff_coe_lt.mp hzb
          · exact relu_proj
      · right; left
        ext z
        simp only [mem_image, mem_Ioo, mem_Ico, zero_le, true_and]
        apply Iff.intro
        · intro ⟨ y, ⟨ hay, hyb ⟩ , hyz ⟩
          rw [←hyz]
          dsimp [relu]
          simp only [gt_iff_lt]
          refine NNReal.coe_lt_coe.mp ?_
          simp only [NNReal.coe_mk, lt_sup_iff, sup_lt_iff, lt_self_iff_false, and_false, or_false]
          apply And.intro <;> linarith
        · intro hzb
          use NNReal.toReal z
          apply And.intro
          · apply And.intro
            · have ha0' : a < 0 := by
                simp only [gt_iff_lt, not_lt] at ha
                exact lt_of_le_of_ne ha ha0
              have h0z : 0 ≤ (relu z) := by exact zero_le
              have h0z' : a < relu z := by exact lt_of_le_of_lt' h0z ha0'
              rw [relu_proj] at h0z'
              assumption
            · have : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
              rw [proj_relu] at this
              · assumption
              assumption
          · rw [relu_proj]
    · by_cases hab : a ≥ b
      · have : Ioo a b = ∅ := by
          exact Ioo_eq_empty_of_le hab
        rw [this]
        simp only [image_empty, or_true]
      · right; right; left
        ext z
        simp only [mem_image, mem_Ioo, mem_singleton_iff]
        constructor
        · rintro ⟨ y, hy, hyz ⟩
          have : y ≤ 0 := by linarith
          have h' := proj_relu' this
          rw [hyz] at h'
          exact NNReal.coe_eq_zero.mp h'
        · intro hz
          have hab' : a < b := by linarith
          use (a + b) / 2
          apply And.intro
          · apply And.intro
            · exact left_lt_add_div_two.mpr hab'
            · exact add_div_two_lt_right.mpr hab'
          · have hn : (a + b) / 2 ≤ 0 := by linarith
            rw [hz]
            apply NNReal.coe_eq_zero.mp
            exact proj_relu' hn

lemma relu_iio (b : Real) :
  ((relu '' (Set.Iio b) = Set.Ico 0 (relu b)) ∨
  (relu '' (Set.Iio b) = { 0 })) := by
    by_cases hb : b > 0
    · left
      ext z
      simp only [mem_image, mem_Iio, mem_Ico, zero_le, true_and]
      apply Iff.intro
      · intro ⟨ x, ⟨  hxb, hxz ⟩ ⟩
        rw [←hxz]
        simp only [gt_iff_lt]
        dsimp [relu]
        apply NNReal.coe_lt_coe.mp
        simp only [NNReal.coe_mk, lt_sup_iff, sup_lt_iff, lt_self_iff_false, and_false, or_false]
        apply And.intro
        · assumption
        · assumption
      · intro hzb
        use z.1
        apply And.intro
        · exact Nonneg.toNonneg_lt.mp hzb
        · have : z ≥ 0 := by exact zero_le
          simp only [NNReal.val_eq_coe]
          exact relu_proj
    · right
      ext z
      simp only [mem_image, mem_Iio, mem_singleton_iff]
      apply Iff.intro
      · intro ⟨ x, ⟨ hxb, hxz ⟩ ⟩
        have : x ≤ 0 := by linarith
        have hn := proj_relu' this
        rw [hxz] at hn
        exact NNReal.coe_eq_zero.mp hn
      · intro hz
        use b - 1
        simp only [sub_lt_self_iff, zero_lt_one, true_and]
        have : b - 1 ≤ 0 := by linarith
        have hn := proj_relu' this
        rw [hz]
        simp only [NNReal.coe_eq_zero] at hn
        assumption

lemma relu_univ : (relu '' univ = univ) := by
  ext z
  simp only [image_univ, mem_range, mem_univ, iff_true]
  use z.1
  apply relu_proj

lemma relu_ioi (b : Real) :
  ((relu '' (Set.Ioi b) = Set.Ioi (relu b)) ∨
  (relu '' (Set.Ioi b) = univ)) := by
  by_cases hb : b > 0
  · left
    ext z
    simp only [mem_image, mem_Ioi]
    apply Iff.intro
    · intro ⟨ x, ⟨ hbx, hxz ⟩ ⟩
      rw [←hxz]
      apply NNReal.coe_lt_coe.mp
      rw [proj_relu, proj_relu]
      · linarith
      · linarith
      linarith
    · intro hbz
      use z.1
      apply And.intro
      · simp only [NNReal.val_eq_coe]
        refine (Real.toNNReal_lt_iff_lt_coe ?_).mp hbz
        linarith
      · apply relu_proj
  · by_cases hb' : b = 0
    · left
      rw [hb']
      ext z
      simp only [mem_image, mem_Ioi]
      apply Iff.intro
      · intro ⟨ x, ⟨ hbx, hxz ⟩ ⟩
        rw [relu_zero]
        rw [←hxz]
        apply NNReal.coe_pos.mp
        rw [proj_relu]
        · assumption
        assumption
      · intro hz
        use z.1
        apply And.intro
        · rw [relu_zero] at hz
          exact hz
        apply relu_proj
    · right
      ext z
      simp only [mem_image, mem_Ioi, mem_univ, iff_true]
      use z.1
      simp only [NNReal.val_eq_coe]
      apply And.intro
      · have : 0 ≤ NNReal.toReal z := by exact NNReal.zero_le_coe
        have this' : b < 0 := by
          simp only [gt_iff_lt, not_lt] at hb
          exact lt_of_le_of_ne hb hb'
        exact lt_of_le_of_lt' this this'
      · exact relu_proj

lemma a_and_b (U : Set NNReal) (ε : Real) (εpos : ε > 0) (A : Set NNReal) (B : Set NNReal)
    (openA : IsOpen A) (openB : IsOpen B)
                (hp : IsPreconnected U)
                (interval : Set NNReal)
                (interval_def : interval = Set.Ioo (0 : NNReal) (NNReal.mk ε (by linarith)))
                (h1' : interval ⊆ A ∪ B)
                (empty : ¬ (interval ∩ B).Nonempty)
                (hA : (U \ {0} ∩ A).Nonempty) (hB : (U \ {0} ∩ B).Nonempty)
                (hAB : U \ {0} ⊆ A ∪ B) : (U \ {0} ∩ (A ∩ B)).Nonempty := by
        let interval' := Set.Iio (NNReal.mk ε (by linarith))
        let A' := A ∪ interval'
        have openA' : IsOpen A' := by
          apply IsOpen.union openA
          exact isOpen_Iio
        let B' := B ∩ Set.Ioi 0
        have openB' : IsOpen B' := by
          exact IsOpen.inter openB isOpen_Ioi
        specialize hp A' B' openA' openB'
        have h1 : U ⊆ A' ∪ B' := by
          intro x hx
          by_cases h0' : x = 0
          · rw [h0']
            simp only [mem_union]
            left
            exact mem_union_right A εpos
          · have : x ∈ U \ { 0 } := by exact mem_sdiff_of_mem hx h0'
            specialize hAB this
            simp only [mem_union]
            rcases hAB with (hAB|hAB)
            · left
              exact mem_union_left interval' hAB
            · right
              apply (mem_inter_iff x B (Ioi 0)).mpr
              apply And.intro
              · assumption
              · apply mem_Ioi.mpr
                exact pos_iff_ne_zero.mpr h0'
        have h2 : (U ∩ A').Nonempty := by
          rcases hA with ⟨ x, hx ⟩
          use x
          simp only [mem_inter_iff]
          apply And.intro
          · have : x ∈ U \ {0} := by exact mem_of_mem_inter_left hx
            exact mem_of_mem_sdiff this
          · apply (mem_union x A interval').mpr
            left
            exact mem_of_mem_inter_right hx
        have h3 : (U ∩ B').Nonempty := by
          rcases hB with ⟨ x, hx ⟩
          use x
          simp only [mem_inter_iff]
          apply And.intro
          · have : x ∈ U \ { 0 } := by exact mem_of_mem_inter_left hx
            exact mem_of_mem_sdiff this
          · apply (mem_inter_iff x B (Ioi 0)).mpr
            apply And.intro
            · exact mem_of_mem_inter_right hx
            · apply mem_Ioi.mpr
              have : x ∈ U \ { 0 } := by exact mem_of_mem_inter_left hx
              have this' : x ∉ ({ 0 } : Set NNReal) := by exact notMem_of_mem_sdiff this
              exact pos_iff_ne_zero.mpr this'
        specialize hp h1 h2 h3
        rcases hp with ⟨ x, hx ⟩
        use x
        simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
        have hn0 : x ≠ 0 := by
          have : x ∈ A' ∩ B' := by exact mem_of_mem_inter_right hx
          have : x ∈ B' := by exact mem_of_mem_inter_right this
          have : x ∈ Set.Ioi 0 := by exact mem_of_mem_inter_right this
          exact pos_iff_ne_zero.mp this
        apply And.intro
        · apply And.intro
          · exact mem_of_mem_inter_left hx
          · exact hn0
        · apply And.intro
          · have : x ∈ A' ∩ B' := by exact mem_of_mem_inter_right hx
            have : x ∈ A' := by exact mem_of_mem_inter_left this
            simp only [A'] at this
            rcases this with (this|this)
            · assumption
            · have hi : x ∈ interval := by
                rw [interval_def]
                simp only [mem_Ioo]
                dsimp [interval'] at this
                simp only [mem_Iio] at this
                apply And.intro
                · exact pos_iff_ne_zero.mpr hn0
                · exact this
              have this' := h1' hi
              rcases this' with (this'|this')
              · assumption
              · exfalso
                apply empty
                use x
                exact mem_inter hi this'
          · have : x ∈ A' ∩ B' := by exact mem_of_mem_inter_right hx
            have : x ∈ B' := by exact mem_of_mem_inter_right this
            exact mem_of_mem_inter_left this

lemma remove_zero_connected (U : Set NNReal) (h0 : 0 ∈ U) (hu : IsOpen U) (hc : IsConnected U) :
  IsConnected (U \ {0}) := by
  rcases Metric.isOpen_iff.mp hu 0 h0 with ⟨ ε, εpos, hε ⟩
  dsimp [IsConnected]
  apply And.intro
  · let ε' : NNReal := NNReal.mk (ε/2) (by linarith)
    have : ε' ∈ Metric.ball 0 ε := by
      simp only [Metric.mem_ball]
      dsimp [ε']
      have hd : dist ε' 0 = ε/2 := by
        rw [NNReal.dist_eq]
        simp only [ε', NNReal.coe_mk, NNReal.coe_zero, sub_zero]
        exact abs_of_nonneg (by linarith)
      rw [hd]
      simp only [half_lt_self_iff, gt_iff_lt]
      linarith
    use ε'
    apply mem_sdiff_singleton.mpr
    apply And.intro
    · exact hε this
    · apply NNReal.coe_ne_zero.mp
      simp only [ne_eq, NNReal.coe_eq_zero]
      dsimp [ε']
      apply NNReal.coe_ne_zero.mp
      simp only [NNReal.coe_mk, ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
      exact ne_of_gt εpos
  · dsimp [IsPreconnected]
    by_contra h
    simp only [not_forall] at h
    rcases h with ⟨ A, B, openA, openB, hAB, hA, hB, hn ⟩
    have hp : IsPreconnected U := IsConnected.isPreconnected hc
    let interval := Set.Ioo (0 : NNReal) (NNReal.mk ε (by linarith))
    have h1' : interval ⊆ A ∪ B := by
      intro x hx
      apply hAB
      simp only [mem_sdiff, mem_singleton_iff]
      apply And.intro
      · apply hε
        simp only [Metric.mem_ball]
        simp only [interval, mem_Ioo] at hx
        rw [NNReal.dist_eq]
        simp only [NNReal.coe_zero, sub_zero, NNReal.abs_eq]
        exact hx.right
      · by_contra h0
        rw [h0] at hx
        simp only [interval, mem_Ioo, lt_self_iff_false, false_and] at hx
    have cb : IsPreconnected interval := isPreconnected_Ioo
    specialize cb A B openA openB h1'
    have iu : interval ⊆ U := by
      intro x hx
      simp only [interval, mem_Ioo] at hx
      apply hε
      simp only [Metric.mem_ball]
      rw [NNReal.dist_eq]
      simp only [NNReal.coe_zero, sub_zero, NNReal.abs_eq]
      exact hx.right
    have hn' : ¬ (interval ∩ (A ∩ B)).Nonempty := by
      by_contra hn''
      rcases hn'' with ⟨ x, hn'' ⟩
      apply hn
      use x
      apply (mem_inter_iff x (U \ {0}) (A ∩ B)).mpr
      apply And.intro
      · apply mem_sdiff_singleton.mpr
        apply And.intro
        · have : x ∈ interval := by exact mem_of_mem_inter_left hn''
          apply iu
          assumption
        · have : x ∈ interval := by exact mem_of_mem_inter_left hn''
          by_contra x0
          rw [x0] at this
          simp only [interval, mem_Ioo, lt_self_iff_false, false_and] at this
      · exact mem_of_mem_inter_right hn''
    have empty : (¬ (interval ∩ A).Nonempty ∨ ¬ (interval ∩ B).Nonempty) := by tauto
    apply hn
    rcases empty with (empty|empty)
    · have h1'' : interval ⊆ B ∪ A := by
        intro x hx
        simp only [mem_union]
        specialize h1' hx
        simp only [mem_union] at h1'
        tauto
      have hBA : U \ {0} ⊆ B ∪ A := by
        intro x hx
        simp only [mem_union]
        specialize hAB hx
        simp only [mem_union] at hAB
        tauto
      have := a_and_b U ε εpos B A openB openA hp interval (by exact rfl) h1'' empty hB hA hBA
      rcases this with ⟨ x, hx ⟩
      use x
      simp only [mem_inter_iff]
      simp only [mem_inter_iff] at hx
      tauto
    · exact a_and_b U ε εpos A B openA openB hp interval (by exact rfl) h1' empty hA hB hAB

lemma zero_in_open (a b : NNReal) (h : IsOpen ((Ioo a b) ∪ {0})) : a ≤ 0 ∧ 0 < b := by
  by_contra h'
  simp only [nonpos_iff_eq_zero, not_and, not_lt] at h'
  by_cases ha : a = 0
  · specialize h' ha
    rw [ha] at h
    rw [h'] at h
    simp only [lt_self_iff_false, not_false_eq_true, Ioo_eq_empty, union_singleton,
      insert_empty_eq] at h
    have : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
    apply this
    assumption
  · let U := Set.Iio (a / 2)
    have openU : IsOpen U := by exact isOpen_Iio
    let U' := U ∩ (Ioo a b ∪ {0})
    let openU' : IsOpen U' := by exact IsOpen.inter openU h
    have U0 : U' = { 0 } := by
      ext x
      simp only [mem_singleton_iff]
      apply Iff.intro
      · intro hx
        dsimp [U, U'] at hx
        simp only [union_singleton, mem_inter_iff, mem_Iio, mem_insert_iff, mem_Ioo] at hx
        have hx1 := hx.1
        have hx2 := hx.2
        rcases hx2 with (hx2|hx2)
        · exact hx2
        · have : a < x := hx2.1
          exfalso
          have this' : a < a / 2 := by exact gt_trans hx1 this
          have this'' : a.toReal < a.toReal / 2 := by exact this'
          have this3 : 0 ≤ a.toReal := by exact NNReal.zero_le_coe
          linarith
      · intro hx
        dsimp [U, U']
        simp only [union_singleton, mem_inter_iff, mem_Iio, mem_insert_iff, mem_Ioo]
        apply And.intro
        · rw [hx]
          have : 0 < a := by exact pos_iff_ne_zero.mpr ha
          exact half_pos this
        · left; assumption
    have : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
    apply this
    rwa [U0] at openU'

private theorem classify_nnreal_of_real_Ioo (U : Set NNReal) (hu : IsOpen U)
    (hr : relu ⁻¹' (U ∩ Ioi 0) = Ioi (0 : ℝ) ∩ NNReal.toReal '' U)
    (h0u0 : 0 ∉ U ∩ Ioi 0) (h0u' : 0 ∉ relu ⁻¹' (U ∩ Ioi 0))
    (c : ∃ a b : ℝ, Ioo a b = relu ⁻¹' (U ∩ Ioi 0)) :
    (∃ x y, Set.Ioo x y = U) ∨ (∃ x : NNReal, Set.Iio x = U) ∨
      (∃ x : NNReal, Set.Ioi x = U) ∨ U = univ := by
  let U0 := U ∩ Ioi 0
  let U' := relu ⁻¹' U0
  change relu ⁻¹' U0 = Ioi (0 : ℝ) ∩ NNReal.toReal '' U at hr
  change 0 ∉ U0 at h0u0
  change 0 ∉ U' at h0u'
  have hu0 : IsOpen U0 := hu.inter isOpen_Ioi
  change ∃ a b : ℝ, Ioo a b = U' at c
  rcases c with ⟨ a, b, c ⟩
  have c' := relu_ioo a b
  have hc := relu_interval_ioo c
  rw [hc] at c'
  by_cases hu0' : 0 ∈ U
  · have uu0 : U = U0 ∪ { 0 } := by
      ext x
      simp only [union_singleton, mem_insert_iff]
      apply Iff.intro
      · intro hx
        dsimp [U0]
        simp only [mem_inter_iff, mem_Ioi]
        by_cases h : x = 0
        · left; exact h
        · right; apply And.intro
          · assumption
          · exact pos_iff_ne_zero.mpr h
      · intro hx
        rcases hx with (hx|hx)
        · rw [hx]
          assumption
        · dsimp [U0] at hx
          simp only [mem_inter_iff, mem_Ioi] at hx
          exact hx.1
    rw [uu0]
    rcases c' with (c'|c'|c'|c')
    · right
      left
      rw [c']
      rw [c'] at uu0
      rw [uu0] at hu
      have hz := zero_in_open (relu a) (relu b) hu
      use relu b
      ext x
      simp only [mem_Iio, union_singleton, mem_insert_iff, mem_Ioo]
      apply Iff.intro
      · intro hx
        by_cases h0 : x = 0
        · left; exact h0
        · right
          apply And.intro
          · have : 0 < x := by exact pos_iff_ne_zero.mpr h0
            exact lt_of_le_of_lt hz.1 this
          · assumption
      · intro hx
        rcases hx with (hx|hx)
        · rw [hx]
          exact hz.2
        · exact hx.2
    · by_cases hb : relu b = 0
      · rw [hb] at c'
        simp only [lt_self_iff_false, not_false_eq_true, Ico_eq_empty] at c'
        rw [c'] at uu0
        simp only [union_singleton, insert_empty_eq] at uu0
        rw [uu0] at hu
        have : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
        exfalso
        exact this hu
      · right
        left
        use relu b
        rw [c']
        ext x
        simp only [mem_Iio, union_singleton, mem_insert_iff, mem_Ico, zero_le, true_and,
          iff_or_self]
        intro hx
        rw [hx]
        exact pos_iff_ne_zero.mpr hb
    · rw [c'] at hu0
      exfalso
      have this' : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
      exact this' hu0
    · rw [c'] at uu0
      simp only [union_singleton, insert_empty_eq] at uu0
      have : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
      rw [uu0] at hu
      exfalso
      exact this hu
  · have uu0 : U = U0 := by
      dsimp [U0]
      simp only [left_eq_inter]
      intro x hx
      simp only [mem_Ioi]
      have : x ≠ 0 := by exact ne_of_mem_of_not_mem hx hu0'
      exact pos_iff_ne_zero.mpr this
    rw [←uu0] at c'
    rcases c' with (c'|c'|c'|c')
    · left
      use relu a
      use relu b
      rw [c']
    · right
      left
      use (relu b)
      rw [c']
      ext x
      simp only [mem_Iio, mem_Ico, zero_le, true_and]
    · rw [c'] at hu
      exfalso
      have : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
      apply this
      exact hu
    · left
      use 0
      use 0
      rw [c']
      simp only [lt_self_iff_false, not_false_eq_true, Ioo_eq_empty]

private theorem classify_nnreal_of_real_Ioi (U : Set NNReal) (hu : IsOpen U) (hc : IsConnected U)
    (hr : relu ⁻¹' (U ∩ Ioi 0) = Ioi (0 : ℝ) ∩ NNReal.toReal '' U)
    (h0u0 : 0 ∉ U ∩ Ioi 0) (h0u' : 0 ∉ relu ⁻¹' (U ∩ Ioi 0))
    (c : ∃ a : ℝ, Ioi a = relu ⁻¹' (U ∩ Ioi 0)) :
    (∃ x y, Set.Ioo x y = U) ∨ (∃ x : NNReal, Set.Iio x = U) ∨
      (∃ x : NNReal, Set.Ioi x = U) ∨ U = univ := by
  let U0 := U ∩ Ioi 0
  let U' := relu ⁻¹' U0
  change relu ⁻¹' U0 = Ioi (0 : ℝ) ∩ NNReal.toReal '' U at hr
  change 0 ∉ U0 at h0u0
  change 0 ∉ U' at h0u'
  have hu0 : IsOpen U0 := hu.inter isOpen_Ioi
  change ∃ x : ℝ, Ioi x = U' at c
  rcases c with ⟨ x, c ⟩
  by_cases h0 : x = 0
  · by_cases hu0 : 0 ∈ U
    · right; right; right
      rw [h0] at c
      dsimp [U'] at c
      ext z
      simp only [mem_univ, iff_true]
      by_cases hz0 : z = 0
      · rw [hz0]
        assumption
      · have zpos : z > 0 := by
          exact pos_iff_ne_zero.mpr hz0
        have zi : z ∈ Set.Ioi 0 := by exact zpos
        have zi' : NNReal.toReal z ∈ relu ⁻¹' U0 := by
          rw [←c]
          simp only [mem_Ioi, NNReal.coe_pos]
          assumption
        simp only [mem_preimage] at zi'
        rw [relu_proj] at zi'
        exact mem_of_mem_inter_left zi'
    · right; right; left
      use 0
      have uu0 : U = U0 := by
        ext z
        apply Iff.intro
        · intro hz
          dsimp [U0]
          simp only [mem_inter_iff, mem_Ioi]
          apply And.intro
          · exact hz
          · have : z ≠ 0 := by exact ne_of_mem_of_not_mem hz hu0
            exact pos_iff_ne_zero.mpr this
        · intro hz
          exact mem_of_mem_inter_left hz
      rw [uu0]
      rw [h0] at c
      ext z
      simp only [mem_Ioi]
      apply Iff.intro
      · intro hz
        have : NNReal.toReal z > 0 := by exact hz
        have this' : NNReal.toReal z ∈ U' := by
          rw [←c]
          simp only [mem_Ioi, NNReal.coe_pos]
          assumption
        dsimp [U'] at this'
        simp only [mem_preimage] at this'
        rw [relu_proj] at this'
        assumption
      · intro hz
        rw [←uu0] at hz
        have : z ≠ 0 := by exact ne_of_mem_of_not_mem hz hu0
        exact pos_iff_ne_zero.mpr this
  · by_cases hx : x < 0
    · have : 0 ∈ U' := by
        have this' : 0 ∈ Set.Ioi x := by exact hx
        rw [c] at this'
        assumption
      exfalso
      exact h0u' this
    · right; right; left
      by_cases hu0 : 0 ∈ U
      · have : U = U0 ∪ {0} := by
          ext z
          simp only [union_singleton, mem_insert_iff]
          apply Iff.intro
          · intro hz
            by_cases hz' : z = 0
            · left; assumption
            · right
              dsimp [U0]
              refine (mem_inter_iff z U (Ioi 0)).mpr ?_
              apply And.intro
              · assumption
              · simp only [mem_Ioi]
                exact pos_iff_ne_zero.mpr hz'
          · intro hz
            rcases hz with (hz|hz)
            · rw [hz]
              assumption
            · exact mem_of_mem_inter_left hz
        dsimp [U'] at c
        rw [hr] at c
        have contra : ¬ IsConnected U := by
          dsimp [IsConnected]
          simp only [not_and]
          intro hn
          dsimp [IsPreconnected]
          simp only [not_forall]
          have xpos : x ≥ 0 := by linarith
          use Set.Iio (NNReal.mk x xpos)
          use Set.Ioi (NNReal.mk x xpos)
          simp only [exists_prop, Iio_union_Ioi, subset_compl_singleton_iff]
          apply And.intro
          · exact isOpen_Iio
          · apply And.intro
            · exact isOpen_Ioi
            · apply And.intro
              · by_contra h
                have h' : NNReal.toReal (NNReal.mk x xpos) ∈ NNReal.toReal '' U :=
                  mem_image_of_mem NNReal.toReal h
                have h'' : NNReal.toReal (NNReal.mk x xpos) ∈ Set.Ioi 0 := by
                  apply mem_Ioi.mpr
                  exact lt_of_le_of_ne xpos fun a => h0 (id (Eq.symm a))
                have h3 : NNReal.toReal (NNReal.mk x xpos)  ∈ Set.Ioi x := by
                  rw [c]
                  exact mem_inter h'' h'
                simp only [NNReal.coe_mk, mem_Ioi, lt_self_iff_false] at h3
              · apply And.intro
                · use 0
                  simp only [mem_inter_iff, mem_Iio]
                  apply And.intro
                  · assumption
                  · apply NNReal.coe_pos.mp
                    simp only [NNReal.coe_mk]
                    exact lt_of_le_of_ne xpos fun a => h0 (id (Eq.symm a))
                · apply And.intro
                  · apply inter_nonempty.mpr
                    use (1 : NNReal) + (NNReal.mk x xpos)
                    apply And.intro
                    · have : 1 + x ∈ Set.Ioi x := by
                        apply mem_Ioi.mpr
                        exact lt_one_add x
                      rw [c] at this
                      simp only [mem_inter_iff, mem_Ioi, mem_image] at this
                      rcases this with ⟨ tpos, ⟨ t, ⟨ tu, ht ⟩  ⟩  ⟩
                      have ht2 : t = 1 + (NNReal.mk x xpos) := by
                        exact NNReal.eq ht
                      rw [←ht2]
                      assumption
                    · apply mem_Ioi.mpr
                      exact lt_one_add ((NNReal.mk x xpos) : NNReal)
                  · refine not_nonempty_iff_eq_empty.mpr ?_
                    let x' : NNReal := (NNReal.mk x xpos)
                    have : (Set.Iio x' ∩ Set.Ioi x') = ∅ := by
                      ext z
                      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false,
                        iff_false, not_and, not_lt]
                      intro hz
                      exact le_of_lt hz
                    rw [this]
                    simp only [inter_empty]
        exfalso
        exact contra hc
      · have h0' : 0 ∉ Set.Ioi x := by exact Eq.mpr_not (congrFun c 0) h0u'
        simp only [mem_Ioi, not_lt] at h0'
        use (NNReal.mk x h0')
        ext z
        simp only [mem_Ioi]
        apply Iff.intro
        · intro hxz
          have hu' : NNReal.toReal z ∈ U' := by
            rw [←c]
            simp only [mem_Ioi]
            exact hxz
          have : NNReal.toReal z ∈ Ioi 0 ∩ NNReal.toReal '' U := by
            rw [←hr]
            exact hu'
          have this' : NNReal.toReal z ∈ NNReal.toReal '' U := mem_of_mem_inter_right this
          simp only [mem_image, NNReal.coe_inj, exists_eq_right] at this'
          assumption
        · intro hz
          apply NNReal.coe_lt_coe.mp
          simp only [NNReal.coe_mk]
          dsimp [U'] at c
          have z0 : z ∈ U0 := by
            refine (mem_inter_iff z U (Ioi 0)).mpr ?_
            apply And.intro
            · exact hz
            · refine mem_Ioi.mpr ?_
              refine NNReal.coe_pos.mp ?_
              simp only [NNReal.coe_pos]
              have hz0 : z ≠ 0 := by exact ne_of_mem_of_not_mem hz hu0
              exact pos_iff_ne_zero.mpr hz0
          have : NNReal.toReal z ∈ Set.Ioi 0 ∩ NNReal.toReal '' U := by
            simp only [mem_inter_iff, mem_Ioi, NNReal.coe_pos, mem_image, NNReal.coe_inj,
              exists_eq_right]
            apply And.intro
            · have : z ≠ 0 := by exact ne_of_mem_of_not_mem hz hu0
              have this' : z ≥ 0 := by exact zero_le
              exact pos_iff_ne_zero.mpr this
            assumption
          rw [←hr] at this
          rw [←c] at this
          simp only [mem_Ioi] at this
          assumption

theorem classify_connected_nnreal_interval (U : Set NNReal) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : NNReal), (Set.Iio x = U)) ∨
  (∃ (x : NNReal), (Set.Ioi x = U)) ∨
  (U = univ) := by
    let U0 := U ∩ (Set.Ioi 0)
    have hu0 : IsOpen U0 := IsOpen.inter hu isOpen_Ioi
    let U' := relu ⁻¹' U0
    have hr : (relu ⁻¹' U0) = (Set.Ioi (0 : Real)) ∩ (NNReal.toReal '' U) := by
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_Ioi, mem_image]
      constructor
      · intro h
        have : U0 ⊆ Set.Ioi 0 := inter_subset_right
        have hr : relu x ∈ Set.Ioi 0 := this h
        simp at hr
        have hr' : 0 < x := Real.toNNReal_pos.mp (this h)
        constructor
        · exact hr'
        · use relu x
          constructor
          · have : U0 ⊆ U := by exact inter_subset_left
            exact this h
          · have hf : (relu x).1 = x := by
              apply proj_relu
              assumption
            assumption
      · rintro ⟨h1,⟨y,⟨hu,hy⟩⟩⟩
        rw [←hy]
        rw [relu_proj]
        apply mem_inter hu
        rw [←hy] at h1
        exact h1
    have hu' : IsOpen U' := Continuous.isOpen_preimage continuous_relu U0 hu0
    have hc' : IsConnected U' := by
     by_cases h0 : 0 ∈ U
     · dsimp [U']
       rw [hr]
       have hs0 : IsConnected (U \ {0}) := by exact remove_zero_connected U h0 hu hc
       have he : (Ioi 0 ∩ NNReal.toReal '' U) = NNReal.toReal '' (U \ {0}) := by
         ext z
         simp only [mem_inter_iff, mem_Ioi, mem_image, mem_sdiff, mem_singleton_iff]
         apply Iff.intro
         · intro ⟨ zpos, ⟨ x, ⟨ hx, hx' ⟩ ⟩  ⟩
           use x
           apply And.intro
           · apply And.intro
             · assumption
             · by_contra h'
               rw [h'] at hx'
               simp only [NNReal.coe_zero] at hx'
               rw [←hx'] at zpos
               exact (lt_self_iff_false 0).mp zpos
           · assumption
         · intro ⟨ x, ⟨ ⟨ h1, h2 ⟩, h3 ⟩ ⟩
           apply And.intro
           · rw [←h3]
             simp only [NNReal.coe_pos]
             exact pos_iff_ne_zero.mpr h2
           · use x
       rw [he]
       have : Continuous NNReal.toReal := by exact NNReal.continuous_coe
       apply IsConnected.image hs0 NNReal.toReal
       apply Continuous.continuousOn
       exact this
     · have he : U' = NNReal.toReal '' U := by
         ext z
         simp only [mem_image]
         apply Iff.intro
         · intro hz
           dsimp [U'] at hz
           rw [hr] at hz
           simp only [mem_inter_iff, mem_Ioi, mem_image] at hz
           rcases hz with ⟨ hzpos, hz ⟩
           assumption
         · rintro ⟨ x, ⟨ hx, hz ⟩ ⟩
           apply mem_preimage.mpr
           rw [←hz]
           rw [relu_proj]
           dsimp [U0]
           simp only [mem_inter_iff, mem_Ioi]
           apply And.intro
           · assumption
           · have : x ≥ 0 := by exact zero_le
             have this' : x ≠ 0 := by exact ne_of_mem_of_not_mem hx h0
             exact pos_iff_ne_zero.mpr this'
       rw [he]
       apply IsConnected.image hc NNReal.toReal
       have : Continuous NNReal.toReal := by exact NNReal.continuous_coe
       apply Continuous.continuousOn
       assumption
    let c := classify_connected_interval U' hu' hc'
    have h0u0 : 0 ∉ U0 := by
      apply zero_notMem_iff.mpr
      intro z hz
      have : z ∈ Set.Ioi (0 : NNReal) := mem_of_mem_inter_right hz
      exact this
    have h0u' : 0 ∉ U' := by
      dsimp [U']
      simp only [mem_preimage]
      rw [relu_zero]
      assumption
    rcases c with (c|c|c|c)
    · exact classify_nnreal_of_real_Ioo U hu hr h0u0 h0u' c
    · rcases c with ⟨ x, hx ⟩
      rw [hx] at h0u'
      simp only [mem_Iio, not_lt] at h0u'
      dsimp [U'] at hx
      rw [hr] at hx
      have hxi : x - 1 ∈ Set.Iio x := by
        apply mem_Iio.mpr
        linarith
      rw [←hx] at hxi
      have hc : x - 1 ∈ Set.Ioi 0 := by exact mem_of_mem_inter_left hxi
      simp only [mem_Ioi, sub_pos] at hc
      linarith
    · exact classify_nnreal_of_real_Ioi U hu hc hr h0u0 h0u' c
    · exfalso
      have h0i : 0 ∉ Set.Ioi (0 : NNReal) := self_notMem_Ioi
      have this' : 0 ∈ U0 := by
        have : 0 ∈ U' := by
          rw [c]
          exact trivial
        dsimp [U'] at this
        simp only [mem_preimage] at this
        rw [relu_zero] at this
        assumption
      exact h0u0 this'

end OneMfld
