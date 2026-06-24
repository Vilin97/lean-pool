/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
import LeanPool.ZFLean.Functions

/-!
# LeanPool.ZFLean.Isomorphisms

Imported Lean Pool material for `LeanPool.ZFLean.Isomorphisms`.
-/
namespace ZFSet
/-- Imported ZFLean declaration. -/
def isIso (A B : ZFSet) : Prop :=
  ∃ (bij : ZFSet) (is_func : A.IsFunc B bij), bij.IsBijective is_func
/-- Imported ZFLean declaration. -/
infix:40 " ≅ᶻ " => ZFSet.isIso
theorem isIso_refl (A : ZFSet) : A ≅ᶻ A :=
  ⟨A.Id, Id.IsFunc, Id.IsBijective⟩
instance : Std.Refl ZFSet.isIso where
  refl := isIso_refl
theorem isIso_trans (x y z : ZFSet) (x_iso_y : x ≅ᶻ y) (y_iso_z : y ≅ᶻ z) : x ≅ᶻ z := by
  obtain ⟨bij, is_func, is_bij⟩ := x_iso_y
  obtain ⟨bij', is_func', is_bij'⟩ := y_iso_z
  exists ZFSet.composition bij' bij x y z, ZFSet.IsFunc_of_composition_IsFunc is_func' is_func
  exact ZFSet.IsBijective.composition_of_bijective is_bij is_bij'
instance : Trans ZFSet.isIso ZFSet.isIso ZFSet.isIso where
  trans := isIso_trans _ _ _
theorem isIso_symm : ∀ ⦃x y⦄, ZFSet.isIso x y → ZFSet.isIso y x := by
  intro x y iso
  obtain ⟨bij, is_func, is_bij⟩ := iso
  have := is_func.1
  use bij⁻¹, ?_
  exact inv_bijective_of_bijective is_bij
instance : Std.Symm (α := ZFSet) isIso where
  symm := isIso_symm
instance : IsTrans ZFSet isIso where
  trans := isIso_trans
theorem isIso_equiv : Equivalence ZFSet.isIso where
  refl := isIso_refl
  symm := @isIso_symm
  trans := @isIso_trans
instance : IsEquiv ZFSet isIso where
  refl := isIso_refl
private def C (A B u : ZFSet) : ℕ → ZFSet
  | 0 => A \ B
  | n + 1 => B.sep fun y ↦ ∃ x ∈ C A B u n, x.pair y ∈ u
open Classical in
theorem bijective_of_injective_on_subset {A B : ZFSet}
  (B_sub : B ⊆ A) {u : ZFSet} {hu : A.IsFunc B u} (u_inj : IsInjective u) :
    ∃ (v : ZFSet) (hv : A.IsFunc B v), IsBijective v := by
  let C₀ := A \ B
  have C_sub {n} : C A B u n ⊆ A := by
    induction n with
    | zero =>
      intro x x_mem_C
      rw [C, mem_sdiff] at x_mem_C
      exact x_mem_C.1
    | succ n ih =>
      intro x x_mem_C
      rw [C, mem_sep] at x_mem_C
      exact B_sub x_mem_C.1
  let v := λᶻ : A → B
              | x ↦ if mem_Cn : ∃ n, x ∈ C A B u n then @ᶻu ⟨x, by
                      rw [is_func_dom_eq hu]
                      obtain ⟨_, x_mem_Cn⟩ := mem_Cn
                      apply C_sub x_mem_Cn⟩
                    else x
  have hv : A.IsFunc B v := by
    apply lambda_isFunc
    intro x xA
    split_ifs with mem_Cn
    · apply fapply_mem_range
    · push Not at mem_Cn
      specialize mem_Cn 0
      rw [C, mem_sdiff, not_and, not_not] at mem_Cn
      exact mem_Cn xA
  have v_inj : IsInjective v := by
    intro x y z hx hy hz eq₁ eq₂
    rw [lambda_spec] at eq₁ eq₂
    split_ifs at eq₁ eq₂ with mem_x mem_y mem_y <;> (
      obtain ⟨-, -, rfl⟩ := eq₁
      obtain ⟨-, -, eq⟩ := eq₂)
    · generalize_proofs u_pfun x_dom y_dom at eq
      rw [SetLike.coe_eq_coe] at eq
      obtain ⟨⟩ := IsInjective.apply_inj hu u_inj eq
      rfl
    · generalize_proofs u_pfun u_rel x_dom at eq
      subst y
      obtain ⟨n, mem_x⟩ := mem_x
      push Not at mem_y
      specialize mem_y (n+1)
      rw [C, mem_sep, not_and] at mem_y
      specialize mem_y hz
      push Not at mem_y
      specialize mem_y x mem_x
      nomatch mem_y <| fapply.def u_pfun x_dom
    · generalize_proofs u_pfun u_rel y_dom at eq
      subst z
      obtain ⟨n, mem_y⟩ := mem_y
      push Not at mem_x
      specialize mem_x (n+1)
      rw [C, mem_sep, not_and] at mem_x
      specialize mem_x hz
      push Not at mem_x
      specialize mem_x y mem_y
      nomatch mem_x <| fapply.def u_pfun y_dom
    · exact eq
  have v_surj : IsSurjective v := by classical
    intro y yB
    by_cases y_mem_C : ∃ n, y ∈ C A B u n
    · obtain ⟨n, y_mem_Cn⟩ := y_mem_C
      have : n ≠ 0 := by
        rintro rfl
        rw [C, mem_sdiff] at y_mem_Cn
        nomatch y_mem_Cn.2 yB
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [C, mem_sep] at y_mem_Cn
      obtain ⟨-, x, x_mem_Cn, x_y_u⟩ := y_mem_Cn
      use x, C_sub x_mem_Cn
      rw [lambda_spec]
      refine ⟨C_sub x_mem_Cn, yB, ?_⟩
      rw [dite_cond_eq_true <| eq_true ⟨n, x_mem_Cn⟩,
        fapply.of_pair (is_func_is_pfunc hu) x_y_u]
    · use y, B_sub yB
      rw [lambda_spec]
      refine ⟨B_sub yB, yB, ?_⟩
      rw [dite_cond_eq_false <| eq_false y_mem_C]
  use v, hv, v_inj, v_surj
/--
Cantor–Bernstein theorem: if there are injective functions
`f : A → B` and `g : B → A`, then `A` and `B` are isomorphic.
-/
theorem isIso_of_biembedding {E F f g : ZFSet} {hf : E.IsFunc F f}
  (f_inj : IsInjective f) {hg : F.IsFunc E g} (g_inj : IsInjective g hg) : E ≅ᶻ F := by
  let B := g.Range
  have B_sub : B ⊆ E := sep_subset_self
  let u := composition g f E F B
  have hu : E.IsFunc B u := ZFSet.IsFunc_of_composition_IsFunc (IsFunc.is_func_on_range hg) hf
  have u_inj : IsInjective u := by
    intro x y z hx hy hz eq₁ eq₂
    unfold u at eq₁ eq₂
    simp only [composition, mem_sep, mem_prod, pair_inj, exists_eq_right_right', existsAndEq,
      and_true, exists_eq_left'] at eq₁ eq₂
    obtain ⟨-, x', hx', x_x'_f, x'_z_g⟩ := eq₁
    obtain ⟨-, y', hy', y_y'_f, y'_z_g⟩ := eq₂
    obtain rfl := g_inj x' y' z hx' hy' (B_sub hz) x'_z_g y'_z_g
    exact f_inj x y x' hx hy hx' x_x'_f y_y'_f
  obtain ⟨v, hv, bij⟩ := bijective_of_injective_on_subset B_sub u_inj
  have hg' : F.IsFunc B g := IsFunc.is_func_on_range hg
  have g_bij : IsBijective g hg' := bijective_of_injective hg g_inj
  have h_v_hinv : E.IsFunc F (composition (inv g hg'.1) v E B F) :=
    IsFunc_of_composition_IsFunc (inv_is_func_of_bijective g_bij) hv
  use composition (inv g hg'.1) v E B F, h_v_hinv
  exact IsBijective.composition_of_bijective bij (inv_bijective_of_bijective g_bij)
alias schroeder_bernstein := isIso_of_biembedding
theorem isIso_of_prod {A B C D : ZFSet} (h : A ≅ᶻ C) (h' : B ≅ᶻ D) : A.prod B ≅ᶻ C.prod D := by
  obtain ⟨f₁, hf₁, bij₁⟩ := h
  obtain ⟨f₂, hf₂, bij₂⟩ := h'
  let F := (A.prod B).prod (C.prod D) |>.sep fun z ↦
    ∃ (a b c d : ZFSet), z = (a.pair b).pair (c.pair d) ∧ (a.pair c ∈ f₁) ∧ (b.pair d ∈ f₂)
  use F, ?_
  · and_intros
    · intro ab a'b' cd hab ha'b' hcd habcd ha'b'cd
      simp only [mem_sep, mem_prod, pair_inj, exists_eq_right_right', F] at habcd ha'b'cd
      obtain ⟨⟨⟨a, ha, b, hb, rfl⟩, c, hc, d, hd, rfl⟩, _, _, _, _, ⟨ab_eq, cd_eq⟩, ac_f₁, bd_f₂⟩ :=
        habcd
      rw [pair_inj] at ab_eq cd_eq
      rcases ab_eq with ⟨rfl, rfl⟩
      rcases cd_eq with ⟨rfl, rfl⟩
      obtain ⟨⟨⟨a', ha', b', hb', rfl⟩, -⟩, _, _, _, _, ⟨a'b'_eq, cd_eq⟩, a'c_f₁, b'd_f₂⟩ := ha'b'cd
      rw [pair_inj] at a'b'_eq cd_eq
      rcases a'b'_eq with ⟨rfl, rfl⟩
      rcases cd_eq with ⟨rfl, rfl⟩
      congr
      · exact bij₁.1 _ _ _ ha ha' hc ac_f₁ a'c_f₁
      · exact bij₂.1 _ _ _ hb hb' hd bd_f₂ b'd_f₂
    · intro cd hcd
      rw [mem_prod] at hcd
      obtain ⟨c, hc, d, hd, rfl⟩ := hcd
      obtain ⟨a, ha, ac_f₁⟩ := bij₁.2 c hc
      obtain ⟨b, hb, bd_f₂⟩ := bij₂.2 d hd
      use a.pair b
      and_intros
      · rw [pair_mem_prod]
        exact ⟨ha, hb⟩
      · simp only [mem_sep, mem_prod, pair_inj, exists_eq_right_right', existsAndEq, and_true,
        exists_eq_left', F]
        and_intros
        · exact ha
        · exact hb
        · exact hc
        · exact hd
        · exact ac_f₁
        · exact bd_f₂
  · and_intros
    · intro z hz
      rw [mem_sep] at hz
      exact hz.1
    · intro z hz
      rw [mem_prod] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := hz
      obtain ⟨c, hc, c_unq⟩ := hf₁.2 a ha
      obtain ⟨d, hd, d_unq⟩ := hf₂.2 b hb
      use c.pair d
      and_intros <;> beta_reduce
      · rw [mem_sep, pair_mem_prod, pair_mem_prod, pair_mem_prod]
        and_intros
        · exact ha
        · exact hb
        · exact hf₁.1 hc |> pair_mem_prod.mp |>.2
        · exact hf₂.1 hd |> pair_mem_prod.mp |>.2
        · use a, b, c, d
      · intro y hy
        rw [mem_sep, pair_mem_prod] at hy
        obtain ⟨c', hc', d', hd', rfl⟩ := hy.1.2 |> mem_prod.mp
        simp only [mem_prod, pair_inj, exists_eq_right_right', existsAndEq, and_true,
          exists_eq_left'] at hy
        congr
        · apply c_unq
          exact hy.2.1
        · apply d_unq
          exact hy.2.2
theorem inv_Image_of_bijective {f A B : ZFSet} {hf : A.IsFunc B f}
  (bij : f.IsBijective) {X : ZFSet} (hX : X ⊆ A) :
    f⁻¹[(f[X])] = X := by
  ext1 x
  constructor <;> intro hx
  · simp only [mem_Image, mem_inv] at hx
    obtain ⟨xA, y, ⟨yB, u, uX, fuy⟩, fxy⟩ := hx
    obtain rfl := bij.1 u x y (hf.1 fuy |> pair_mem_prod.mp |>.1) xA yB fuy fxy
    exact uX
  · simp only [mem_Image, mem_inv]
    and_intros
    · exact hX hx
    · obtain ⟨y, yB, -⟩ := hf.2 x (hX hx)
      use y
      and_intros
      · exact hf.1 yB |> pair_mem_prod.mp |>.2
      · use x
      · exact yB
theorem Image_inv_of_bijective {f A B : ZFSet} {hf : A.IsFunc B f}
  (bij : f.IsBijective hf) {X : ZFSet} (hX : X ⊆ B) :
    f[(f⁻¹[X])] = X := by
  let g := f⁻¹
  have hg : B.IsFunc A g := inv_is_func_of_bijective bij
  have gbij : g.IsBijective hg := inv_bijective_of_bijective bij
  have ginv_eq : g⁻¹ = f := by rw [inv_involutive]
  have := inv_Image_of_bijective gbij hX
  dsimp [g] at this
  conv at this =>
    enter [1,1]
    rw [inv_involutive]
  exact this
theorem IsInjective_of_left_inverse {A B : ZFSet} {f : ZFSet}
  (hf : A.IsFunc B f) {g : ZFSet} (hg : B.IsFunc A g) (left_inv : g ∘ᶻ f = 𝟙A) :
    IsInjective f := by
  intro x y z hx hy hz fxy fxz
  have x_x : x.pair x ∈ g ∘ᶻ f := by
    rw [left_inv]
    exact pair_self_mem_Id hx
  have y_y : y.pair y ∈ g ∘ᶻ f := by
    rw [left_inv]
    exact pair_self_mem_Id hy
  simp only [fcomp, composition, mem_sep, mem_prod, pair_inj, exists_eq_right_right', and_self,
    existsAndEq, and_true, exists_eq_left'] at x_x y_y
  obtain ⟨-, x', hx', x_x'_f, x'_x_g⟩ := x_x
  obtain ⟨-, y', hy', y_y'_f, y'_y_g⟩ := y_y
  obtain rfl : x' = y' := by
    trans z
    · apply hf.2 x hx |>.unique
      · exact x_x'_f
      · exact fxy
    · apply hf.2 y hy |>.unique
      · exact fxz
      · exact y_y'_f
  apply hg.2 x' hx' |>.unique
  · exact x'_x_g
  · exact y'_y_g
theorem IsSurjective_of_right_inverse {A B : ZFSet} {f : ZFSet}
  (hf : A.IsFunc B f) {g : ZFSet} (hg : B.IsFunc A g) (right_inv : f ∘ᶻ g = 𝟙B) :
    IsSurjective f := by
  intro y yB
  have y_y : y.pair y ∈ f ∘ᶻ g := by
    rw [right_inv]
    exact pair_self_mem_Id yB
  simp only [fcomp, composition, mem_sep, mem_prod, pair_inj, exists_eq_right_right', and_self,
    existsAndEq, and_true, exists_eq_left'] at y_y
  obtain ⟨yB, x, xA, gyx, fxy⟩ := y_y
  use x, xA
theorem isIso_of_two_sided_inverse {A B : ZFSet} {f : ZFSet}
  {hf : A.IsFunc B f} {g : ZFSet} {hg : B.IsFunc A g}
  (left_inv : g ∘ᶻ f = 𝟙A) (right_inv : f ∘ᶻ g = 𝟙B) :
    A ≅ᶻ B := by
  use f, hf
  and_intros
  · exact IsInjective_of_left_inverse _ _ left_inv
  · exact IsSurjective_of_right_inverse _ _ right_inv
theorem isIso_powerset {A B : ZFSet} (h : A ≅ᶻ B) : A.powerset ≅ᶻ B.powerset := by
  obtain ⟨f, hf, bij⟩ := h
  let F := λᶻ : A.powerset → B.powerset | x ↦ f[x]
  have hF : A.powerset.IsFunc B.powerset F := by
    apply lambda_isFunc
    intros
    rw [mem_powerset]
    intro y yIm
    rw [mem_Image] at yIm
    exact yIm.1
  let F' := λᶻ : B.powerset → A.powerset | z ↦ f⁻¹[z]
  have hF' : B.powerset.IsFunc A.powerset F' := by
    apply lambda_isFunc
    intros
    rw [mem_powerset]
    intro y yIm
    rw [mem_Image] at yIm
    exact yIm.1
  have left_inv : F' ∘ᶻ F = 𝟙A.powerset := by
    ext1 X
    rw [fcomp, composition, mem_sep, mem_prod]
    constructor
    · rintro ⟨⟨X, hX, Y, hY, rfl⟩, ⟨_, _, eq, Z, hZ, FXZ, F'ZY⟩⟩
      rw [pair_inj] at eq
      obtain ⟨rfl, rfl⟩ := eq
      rw [mem_lambda] at FXZ F'ZY
      simp only [pair_inj, mem_powerset, existsAndEq, and_true, exists_eq_left'] at FXZ F'ZY
      obtain ⟨-, -, rfl⟩ := FXZ
      obtain ⟨-, -, rfl⟩ := F'ZY
      rw [inv_Image_of_bijective bij (mem_powerset.mp hX), pair_mem_Id_iff hX]
    · intro hX
      rw [mem_Id_iff] at hX
      obtain ⟨X, hX, rfl⟩ := hX
      simp only [mem_powerset, pair_inj, exists_eq_right_right', and_self, existsAndEq,
        and_true, exists_eq_left']
      apply And.intro <| mem_powerset.mp hX
      use f[X]
      and_intros
      · intro z hz
        rw [mem_Image] at hz
        exact hz.1
      · rw [lambda_spec]
        refine ⟨hX, ?_, rfl⟩
        rw [mem_powerset]
        intro y hy
        rw [mem_Image] at hy
        exact hy.1
      · rw [lambda_spec]
        refine ⟨?_, hX, ?_⟩
        · rw [mem_powerset]
          intro y hy
          rw [mem_Image] at hy
          exact hy.1
        · rw [inv_Image_of_bijective bij (mem_powerset.mp hX)]
  have right_inv : F ∘ᶻ F' = 𝟙B.powerset := by
    ext1 X
    rw [fcomp, composition, mem_sep, mem_prod]
    constructor
    · rintro ⟨⟨X, hX, Y, hY, rfl⟩, ⟨_, _, eq, Z, hZ, FXZ, F'ZY⟩⟩
      rw [pair_inj] at eq
      obtain ⟨rfl, rfl⟩ := eq
      rw [mem_lambda] at FXZ F'ZY
      simp only [pair_inj, mem_powerset, existsAndEq, and_true, exists_eq_left'] at FXZ F'ZY
      obtain ⟨-, -, rfl⟩ := FXZ
      obtain ⟨-, -, rfl⟩ := F'ZY
      rw [Image_inv_of_bijective bij (mem_powerset.mp hX), pair_mem_Id_iff hX]
    · intro hX
      rw [mem_Id_iff] at hX
      obtain ⟨X, hX, rfl⟩ := hX
      simp only [mem_powerset, pair_inj, exists_eq_right_right', and_self, existsAndEq,
        and_true, exists_eq_left']
      apply And.intro <| mem_powerset.mp hX
      have := subset_prod_inv hf.1
      use f⁻¹[X]
      and_intros
      · intro z hz
        rw [mem_Image] at hz
        exact hz.1
      · rw [lambda_spec]
        refine ⟨hX, ?_, rfl⟩
        rw [mem_powerset]
        intro y hy
        rw [mem_Image] at hy
        exact hy.1
      · rw [lambda_spec]
        refine ⟨?_, hX, ?_⟩
        · rw [mem_powerset]
          intro y hy
          rw [mem_Image] at hy
          exact hy.1
        · rw [Image_inv_of_bijective bij (mem_powerset.mp hX)]
  apply isIso_of_two_sided_inverse left_inv right_inv
theorem isIso_of_funs {A B C D : ZFSet} (h : A ≅ᶻ C) (h' : B ≅ᶻ D) : A.funs B ≅ᶻ C.funs D := by
  classical
  obtain ⟨F, hF, Fbij⟩ := h
  have : F⁻¹ ⊆ C.prod A := by apply subset_prod_inv
  obtain ⟨G, hG, Gbij⟩ := h'
  let ξ := λᶻ : (A.funs B) → (C.funs D)
              |     f      ↦ if hf : f ⊆ A.prod B then
                              λᶻ: C → D
                                | c ↦ ⋂₀ (G[f[F⁻¹[{c}]]])
                            else ∅
  use ξ, ?_
  · rw [bijective_exists1_iff]
    intro f hf
    rw [mem_funs] at hf
    have Ginv_isfunc := inv_is_func_of_bijective Gbij
    let g := λᶻ : A → B
                | a ↦ if ha : a ∈ A then ⋂₀ (G⁻¹[f[F[{a}]]]) else ∅
    have hg : A.IsFunc B g := by
      apply lambda_isFunc
      intro a ha
      rw [dite_cond_eq_true (eq_true ha),
        Image_singleton_eq_fapply hF ha,
        Image_singleton_eq_fapply hf (by apply fapply_mem_range),
        Image_singleton_eq_fapply Ginv_isfunc (by apply fapply_mem_range),
        sInter_singleton]
      apply fapply_mem_range
    use g
    and_intros
    · apply mem_funs_of_lambda
      intro a ha
      rw [dite_cond_eq_true (eq_true ha),
        Image_singleton_eq_fapply hF ha,
        Image_singleton_eq_fapply hf (by apply fapply_mem_range),
        Image_singleton_eq_fapply Ginv_isfunc (by apply fapply_mem_range),
        sInter_singleton]
      apply fapply_mem_range
    · rw [lambda_spec]
      refine ⟨mem_funs.mpr hg, mem_funs.mpr hf, ?_⟩
      · rw [dite_cond_eq_true (eq_true hg.1), lambda_eta hf, lambda_ext_iff]
        · intro c hc
          rw [dite_cond_eq_true (eq_true hc)]
          rw [Image_singleton_eq_fapply (inv_is_func_of_bijective Fbij) hc,
            Image_singleton_eq_fapply hg (by apply fapply_mem_range),
            Image_singleton_eq_fapply hG (by apply fapply_mem_range),
            sInter_singleton]
          conv =>
            unfold fapply
            dsimp
            rfl
          congr
          funext d
          ext
          constructor <;> (rintro ⟨xD, h⟩; refine ⟨xD, ?_⟩)
          · generalize_proofs Frel c_Finv c_Finv_g
            have ⟨bB, ab_g⟩ := Classical.choose_spec c_Finv_g
            have ⟨aA, ac_F⟩ := Classical.choose_spec c_Finv
            set b := Classical.choose c_Finv_g
            set a := Classical.choose c_Finv
            rw [mem_inv] at ac_F
            rw [lambda_spec] at ab_g
            obtain ⟨-, -, b_eq⟩ := ab_g
            rw [dite_cond_eq_true (eq_true aA)] at b_eq
            have Fa := fapply.of_pair (is_func_is_pfunc hF) ac_F
            have Fc := fapply.of_pair (is_func_is_pfunc hf) h
            conv at b_eq =>
              enter [2]
              rw [Image_singleton_eq_fapply hF aA, Fa, Image_singleton_eq_fapply hf hc, Fc,
                ←fapply_eq_Image_singleton Ginv_isfunc xD]
            rw [b_eq, ←mem_inv (is_rel_of_is_func hG)]
            apply fapply.def
          · generalize_proofs Frel ac_Finv ab_g_spec at h
            have ⟨aA, ac_F⟩ := Classical.choose_spec ac_Finv
            have ⟨bB, ab_g⟩ := Classical.choose_spec ab_g_spec
            set b := Classical.choose ab_g_spec
            set a := Classical.choose ac_Finv
            rw [lambda_spec] at ab_g
            obtain ⟨-, -, b_eq⟩ := ab_g
            rw [dite_cond_eq_true (eq_true aA)] at b_eq
            rw [mem_inv] at ac_F
            have Fa := fapply.of_pair (is_func_is_pfunc hF) ac_F
            have Gb := fapply.of_pair (is_func_is_pfunc hG) h
            conv at b_eq =>
              enter [2]
              rw [Image_singleton_eq_fapply hF aA, Fa, Image_singleton_eq_fapply hf hc,
                Image_singleton_eq_fapply Ginv_isfunc (fapply_mem_range _ _), sInter_singleton]
            simp only [b_eq, Subtype.ext_iff] at Gb
            conv at Gb =>
              enter [1,1]
              rw [←fapply_composition hG Ginv_isfunc (fapply_mem_range _ _)]
              unfold fapply
            dsimp at Gb
            generalize_proofs Grel cdf cd_GGinv at Gb
            subst d
            have ⟨dD, cd_G⟩ := Classical.choose_spec cd_GGinv
            have ⟨d'D, cd_f⟩ := Classical.choose_spec cdf
            set d := Classical.choose cd_GGinv
            set d' := Classical.choose cdf
            rw [composition_inv_self_of_bijective Gbij, pair_mem_Id_iff d'D] at cd_G
            rwa [←cd_G]
        · intro c hc
          rw [dite_cond_eq_true (eq_true hc)]
          apply fapply_mem_range
    · rintro g' ⟨hg', g'f_ξ⟩
      rw [lambda_spec] at g'f_ξ
      obtain ⟨-,-,f_eq⟩ := g'f_ξ
      rw [dite_cond_eq_true (eq_true (by rw [mem_funs] at hg'; exact hg'.1))] at f_eq
      subst f_eq
      rw [lambda_eta (mem_funs.mp hg'), lambda_ext_iff]
      · intro a ha
        simp only [dite_cond_eq_true (eq_true ha)]
        rw [Image_singleton_eq_fapply hF ha,
          Image_singleton_eq_fapply hf (by apply fapply_mem_range),
          Image_singleton_eq_fapply Ginv_isfunc (by apply fapply_mem_range),
          sInter_singleton]
        conv_rhs =>
          unfold fapply
        dsimp
        generalize_proofs g'pfunc g'rel a_g'dom Grel Frel acF dclambda bdGinv
        have ⟨cC, ac_F⟩ := Classical.choose_spec acF
        have ⟨bB, db_G⟩ := Classical.choose_spec bdGinv
        have ⟨dD, dc_eq⟩:= Classical.choose_spec dclambda
        set! d := Classical.choose dclambda with d_def
        set! b := Classical.choose bdGinv with b_def
        set! c := Classical.choose acF with c_def
        rw [lambda_spec] at dc_eq
        obtain ⟨-, -, d_eq⟩ := dc_eq
        conv_lhs at d_eq => rw [←d_def]
        rw [←mem_inv] at ac_F
        conv at ac_F =>
          conv =>
            lhs
            change inv F
          rw [←c_def]
        conv at d_eq =>
          conv =>
            enter [2,1,2]
            conv =>
              enter [2]
              rw [←c_def, Image_singleton_eq_fapply (inv_is_func_of_bijective Fbij) cC]
              simp only [←c_def, fapply.of_pair _ ac_F]
          conv =>
            enter [2]
            conv =>
              enter [1,2]
              rw [Image_singleton_eq_fapply (mem_funs.mp hg') ha]
            rw [←fapply_eq_Image_singleton hG (fapply_mem_range g'pfunc a_g'dom)]
        rw [←b_def, ←d_def] at db_G
        have b_eq := fapply.of_pair (is_func_is_pfunc Ginv_isfunc) db_G
        rw [Subtype.ext_iff] at b_eq
        simp only [d_eq] at b_eq
        rw [←fapply_composition Ginv_isfunc hG (fapply_mem_range g'pfunc a_g'dom)] at b_eq
        conv at b_eq =>
          unfold fapply
          dsimp
        generalize_proofs abg' bb'GGinv at b_eq
        have ⟨bB', bb'⟩ := Classical.choose_spec bb'GGinv
        have ⟨g'B, ab_g'⟩ := Classical.choose_spec abg'
        set b := Classical.choose bb'GGinv
        set b' := Classical.choose abg'
        rw [composition_self_inv_of_bijective Gbij, pair_mem_Id_iff g'B] at bb'
        rw [←b_def, ←b_eq, ←bb']
        rfl
      · intro _ h
        rw [dite_cond_eq_true (eq_true h)]
        apply fapply_mem_range
  · and_intros
    · exact lambda_subset
    · intro f hf
      rw [mem_funs] at hf
      use λᶻ : C → D
             | c ↦ ⋂₀ (G[f[F⁻¹[{c}]]])
      and_intros <;> beta_reduce
      · rw [lambda_spec]
        and_intros
        · rwa [mem_funs]
        · apply mem_funs_of_lambda
          intro c hc
          obtain ⟨a, ha, a_def⟩ := eq_singleton_of_bijective_inv_Image_of_singleton Fbij hc
          obtain ⟨b, hb, b_def⟩ : ∃ b ∈ B, f[{a}] = {b} := by
            obtain ⟨b, hb, b_unq⟩ := hf.2 a ha
            use b
            and_intros
            · exact hf.1 hb |> pair_mem_prod.mp |>.2
            · rwa [←Image_of_singleton_pair_mem_iff hf]
          obtain ⟨d, hd, d_def⟩ : ∃ d ∈ D, G[{b}] = {d} := by
            obtain ⟨d, hd, d_unq⟩ := hG.2 b hb
            use d
            and_intros
            · exact hG.1 hd |> pair_mem_prod.mp |>.2
            · rwa [←Image_of_singleton_pair_mem_iff hG]
          rwa [a_def, b_def, d_def, sInter_singleton]
        · rw [dite_cond_eq_true (eq_true hf.1)]
      · intro g hg
        rw [lambda_spec, dite_cond_eq_true (eq_true hf.1)] at hg
        exact hg.2.2
theorem isIso_powerset_char_pred {A : ZFSet} : A.powerset ≅ᶻ A.funs 𝔹 := by
  apply isIso_symm
  let f := λᶻ : (A.funs 𝔹) → (A.powerset)
              |         fX ↦ A.sep fun z ↦ z.pair zftrue ∈ fX
  use f, ?_
  · and_intros
    · intro fX fY Z hfX hfY hZ fX_Z fY_Z
      rw [mem_lambda] at fX_Z fY_Z
      obtain ⟨_, X, eq, -, _, rfl⟩ := fX_Z
      rw [pair_inj] at eq
      obtain ⟨rfl, rfl⟩ := eq
      obtain ⟨_, Y, eq, -, _, rfl⟩ := fY_Z
      rw [pair_inj] at eq
      obtain ⟨rfl, hext⟩ := eq
      simp only [ZFSet.ext_iff, mem_sep, and_congr_right_iff] at hext
      ext1 z
      constructor <;> intro hz
      · obtain ⟨a, ha, b, hb, rfl⟩ := (mem_funs.mp hfX).1 hz |> mem_prod.mp
        specialize hext a ha
        rw [ZFBool.mem_𝔹_iff] at hb
        obtain rfl | rfl := hb
        · have : a.pair zftrue ∉ fX := by
            intro contr
            rw [mem_funs] at hfX
            nomatch zftrue_ne_zffalse <| hfX.2 a ha |>.unique contr hz
          rw [iff_false_left this] at hext
          rw [mem_funs] at hfY
          obtain ⟨b', ab', _⟩ := hfY.2 a ha
          obtain rfl | rfl := hfY.1 ab' |> pair_mem_prod.mp |>.2 |> (ZFBool.mem_𝔹_iff b').mp
          · exact ab'
          · contradiction
        · exact hext.mp hz
      · obtain ⟨a, ha, b, hb, rfl⟩ := (mem_funs.mp hfY).1 hz |> mem_prod.mp
        specialize hext a ha
        rw [ZFBool.mem_𝔹_iff] at hb
        obtain rfl | rfl := hb
        · have : a.pair zftrue ∉ fY := by
            intro contr
            rw [mem_funs] at hfY
            nomatch zftrue_ne_zffalse <| hfY.2 a ha |>.unique contr hz
          rw [iff_false_right this] at hext
          rw [mem_funs] at hfX
          obtain ⟨b', ab', _⟩ := hfX.2 a ha
          obtain rfl | rfl := hfX.1 ab' |> pair_mem_prod.mp |>.2 |> (ZFBool.mem_𝔹_iff b').mp
          · exact ab'
          · contradiction
        · exact hext.mpr hz
    · intro X hX
      rw [mem_powerset] at hX
      let fX := A.prod 𝔹 |>.sep fun ab ↦ ab.π₁ ∈ X ↔ ab.π₂ = zftrue
      use fX
      have fX_mem_funs : fX ∈ A.funs 𝔹 := by
        rw [mem_funs]
        and_intros
        · intro z hz
          rw [mem_sep, mem_prod] at hz
          obtain ⟨⟨a, ha, b, hb, rfl⟩, _⟩ := hz
          rw [pair_mem_prod]
          exact ⟨ha, hb⟩
        · intro a ha
          by_cases a_mem_X : a ∈ X
          · use zftrue
            and_intros
            · beta_reduce
              rw [mem_sep, pair_mem_prod]
              and_intros
              · exact ha
              · rw [ZFBool.mem_𝔹_iff]
                right
                rfl
              · rwa [π₁_pair, π₂_pair, iff_true_right rfl]
            · intro b hb
              rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair] at hb
              rwa [←hb.2]
          · use zffalse
            and_intros
            · beta_reduce
              rw [mem_sep, pair_mem_prod]
              and_intros
              · exact ha
              · rw [ZFBool.mem_𝔹_iff]
                left
                rfl
              · rwa [π₁_pair, π₂_pair, iff_false_right zftrue_ne_zffalse.symm]
            · intro b hb
              rw [mem_sep, pair_mem_prod, π₁_pair, π₂_pair, ←not_iff_not] at hb
              exact Or.resolve_right (ZFBool.mem_𝔹_iff b |>.mp hb.1.2) (hb.2.mp a_mem_X)
      and_intros
      · exact fX_mem_funs
      · rw [lambda_spec]
        refine ⟨fX_mem_funs, by rwa [mem_powerset], ?_⟩
        · ext1 z
          rw [mem_sep, mem_sep, pair_mem_prod, π₁_pair, π₂_pair, iff_true_right rfl]
          constructor
          · intro hz
            exact ⟨hX hz, ⟨hX hz, ZFBool.zftrue_mem_𝔹⟩, hz⟩
          · rintro ⟨_, _, hz⟩
            exact hz
  · and_intros
    · intro z hz
      rw [mem_lambda] at hz
      obtain ⟨fX, X, rfl, fX_def, _, rfl⟩ := hz
      rw [pair_mem_prod]
      and_intros <;> assumption
    · intro fX fX_mem
      use A.sep fun z ↦ z.pair zftrue ∈ fX, ?_
      · intro y hy
        unfold f at hy
        rw [lambda_spec] at hy
        exact hy.2.2
      · beta_reduce
        rw [lambda_spec]
        refine ⟨fX_mem, ?_, rfl⟩
        rw [mem_powerset]
        exact sep_subset_self

open Classical in
/-- Imported ZFLean declaration. -/
noncomputable def currify {A B C : ZFSet} (f : ZFSet)
  (hf : (A.prod B).IsFunc C f := by zfun) : ZFSet :=
  λᶻ : A   → (B.funs C)
       | a ↦ if ha : a ∈ A then
                λᶻ : B → C
                   | b ↦ if hb : b ∈ B then
                          @ᶻf ⟨a.pair b, by rw [is_func_dom_eq hf, pair_mem_prod]; exact ⟨ha, hb⟩⟩
                        else ∅
              else ∅
@[zfun]
theorem currify_is_func {A B C : ZFSet} (f : ZFSet)
  (hf : (A.prod B).IsFunc C f := by zfun) : A.IsFunc (B.funs C) (currify f hf) := by
  apply lambda_isFunc
  intro x hx
  rw [dite_cond_eq_true (eq_true hx), mem_funs]
  and_intros
  · exact lambda_subset
  · intro y hy
    obtain ⟨z, hz, z_unq⟩ := hf.2 (x.pair y) (by rw [pair_mem_prod]; exact ⟨hx, hy⟩)
    use z
    and_intros <;> beta_reduce
    · rw [lambda_spec]
      refine ⟨hy, hf.1 hz |> pair_mem_prod.mp |>.2, ?_⟩
      rw [dite_cond_eq_true (eq_true hy), fapply.of_pair (is_func_is_pfunc hf) hz]
    · intro w hw
      rw [lambda_spec, dite_cond_eq_true (eq_true hy)] at hw
      rw [hw.2.2]
      apply z_unq
      apply fapply.def
open Classical in
/-- Imported ZFLean declaration. -/
noncomputable def uncurrify {A B C : ZFSet} (g : ZFSet)
  (hg : A.IsFunc (B.funs C) g := by zfun) : ZFSet :=
  λᶻ : (A.prod B) → C
       | ab ↦
              let a := ab.π₁
              let b := ab.π₂
              if hab : a ∈ A ∧ b ∈ B then
                let f := @ᶻg ⟨a, by
                    rw [is_func_dom_eq hg]
                    exact hab.1
                  ⟩
                have hf := mem_funs.mp f.2
                @ᶻf ⟨b, by
                    rw [is_func_dom_eq hf]
                    exact hab.2
                  ⟩
              else ∅
@[zfun]
theorem uncurrify_is_func {A B C : ZFSet} (g : ZFSet)
  (hg : A.IsFunc (B.funs C) g := by zfun) : (A.prod B).IsFunc C (uncurrify g hg) := by
  apply lambda_isFunc
  intro z hz
  rw [mem_prod] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  rw [dite_cond_eq_true (eq_true (by simp only [π₁_pair, ha, π₂_pair, hb, and_self]))]
  simp only [π₂_pair, SetLike.coe_mem]
@[simp]
theorem currify_of_uncurrify {A B C : ZFSet} (f : ZFSet)
    (hf : (A.IsFunc (B.funs C)) f := by zfun) :
  currify (uncurrify f) = f := by
    simp only [currify, uncurrify, lambda_eta hf]
    rw [lambda_ext_iff]
    · intro x hx
      simp_rw [dite_cond_eq_true (eq_true hx)]
      conv =>
        enter [2,1]
        change ?f_x
      rw [lambda_eta (mem_funs.mp ?f_x.2), lambda_ext_iff]
      · intro y hy
        simp_rw [dite_cond_eq_true (eq_true hy)]
        conv_lhs =>
          rw [
            fapply_lambda
              (by
                intro _ h
                rw [pair_eta h, pair_mem_prod] at h
                rw [dite_cond_eq_true (eq_true h)]
                apply fapply_mem_range)
              (by rw [pair_mem_prod]; exact ⟨hx, hy⟩),
            dite_cond_eq_true (eq_true (by simp only [π₁_pair, π₂_pair, hx, hy, and_self]))]
          simp only [π₁_pair, π₂_pair]
        congr 2
        · simp only [π₁_pair]
        · apply proof_irrel_heq
        · congr 1
          · funext x
            simp only [π₁_pair, mem_sep]
          · apply proof_irrel_heq
      · intro _ h
        rw [dite_cond_eq_true (eq_true h)]
        apply fapply_mem_range
    · intro _ hx
      rw [dite_cond_eq_true (eq_true hx)]
      apply mem_funs_of_lambda
      intro _ hx
      rw [dite_cond_eq_true (eq_true hx)]
      apply fapply_mem_range
theorem uncurrify_of_currify {A B C : ZFSet} (g : ZFSet)
    (hg : (A.prod B).IsFunc C g := by zfun) :
  uncurrify (currify g) = g := by
    simp only [currify, uncurrify, lambda_eta hg]
    rw [lambda_ext_iff]
    · intro ab hab
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp hab
      simp_rw [dite_cond_eq_true (eq_true hab), π₂_pair]
      conv_lhs =>
        rw [dite_cond_eq_true (eq_true (by simp only [π₁_pair, ha, π₂_pair, hb, and_self]))]
        rw [fapply_eq_Image_singleton (by rw [←mem_funs]; apply fapply_mem_range) hb]
        conv =>
          enter [1,1]
          simp only [π₁_pair]
          rw [
            fapply_lambda (by
                intro _ h
                rw [dite_cond_eq_true (eq_true h)]
                apply mem_funs_of_lambda
                intro _ hx
                rw [dite_cond_eq_true (eq_true hx)]
                apply fapply_mem_range
              ) ha,
            dite_cond_eq_true (eq_true ha)]
        rw [←fapply_eq_Image_singleton (lambda_isFunc (fun h ↦ by
              rw [dite_cond_eq_true (eq_true h)]
              apply fapply_mem_range)) hb,
          fapply_lambda (fun h ↦ by rw [dite_cond_eq_true (eq_true h)]; apply fapply_mem_range) hb,
          dite_cond_eq_true (eq_true hb)]
    · intro _ h
      rw [dite_cond_eq_true (eq_true (by rwa [←pair_mem_prod, ←pair_eta h]))]
      apply fapply_mem_range
open Classical in
theorem isIso_curry {A B C : ZFSet} :
  (A.prod B).funs C ≅ᶻ A.funs (B.funs C) := by
  let curry  := λᶻ : (A.prod B).funs C → A.funs (B.funs C)
    | f ↦ if hf : f ∈ (A.prod B).funs C then
            currify f (mem_funs.mp hf)
          else ∅
  let uncurry := λᶻ : A.funs (B.funs C) → (A.prod B).funs C
    | g ↦ if hg : g ∈ A.funs (B.funs C) then
            uncurrify g (mem_funs.mp hg)
          else ∅
  have hcurry : IsFunc ((A.prod B).funs C) (A.funs (B.funs C)) curry := by
    apply lambda_isFunc
    intro f hf
    rw [dite_cond_eq_true (eq_true hf), mem_funs]
    apply currify_is_func
  have huncurry : IsFunc (A.funs (B.funs C)) ((A.prod B).funs C) uncurry := by
    apply lambda_isFunc
    intro g hg
    rw [dite_cond_eq_true (eq_true hg), mem_funs]
    apply uncurrify_is_func
  have l_inv : (uncurry ∘ᶻ curry) = 𝟙((A.prod B).funs C) := by
    rw [is_func_ext_iff (IsFunc_of_composition_IsFunc huncurry hcurry) Id.IsFunc]
    intro f hf
    rw [←SetLike.coe_eq_coe, fapply_Id hf]
    conv_lhs =>
      rw [fapply_composition huncurry hcurry hf]
      unfold uncurry
      rw [
        fapply_lambda (by
            intro _ h
            rw [dite_cond_eq_true (eq_true h), mem_funs]
            apply uncurrify_is_func
          ) (fapply_mem_range _ _),
        dite_cond_eq_true (eq_true (fapply_mem_range _ _))]
      conv =>
        enter [1]
        unfold curry
        rw [
          fapply_lambda (by
              intro _ h
              rw [dite_cond_eq_true (eq_true h), mem_funs]
              apply currify_is_func
            ) hf,
          dite_cond_eq_true (eq_true hf)]
      rw [uncurrify_of_currify f (mem_funs.mp hf)]
  have r_inv : (curry ∘ᶻ uncurry) = 𝟙(A.funs (B.funs C)) := by
    rw [is_func_ext_iff (IsFunc_of_composition_IsFunc hcurry huncurry) Id.IsFunc]
    intro g hg
    rw [←SetLike.coe_eq_coe, fapply_Id hg]
    conv_lhs =>
      rw [fapply_composition hcurry huncurry hg]
      unfold curry
      rw [
        fapply_lambda (by
            intro _ h
            rw [dite_cond_eq_true (eq_true h), mem_funs]
            apply currify_is_func
          ) (fapply_mem_range _ _),
        dite_cond_eq_true (eq_true (fapply_mem_range _ _))]
      conv =>
        enter [1]
        unfold uncurry
        rw [
          fapply_lambda (by
              intro _ h
              rw [dite_cond_eq_true (eq_true h), mem_funs]
              apply uncurrify_is_func
            ) hg,
          dite_cond_eq_true (eq_true hg)]
      rw [currify_of_uncurrify g (mem_funs.mp hg)]
  exact isIso_of_two_sided_inverse l_inv r_inv
end ZFSet
