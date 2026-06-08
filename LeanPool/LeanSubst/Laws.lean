/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren
import LeanPool.LeanSubst.Subst

namespace LeanSubst
  universe u
  variable {S T : Type}

  /-- A `SubstMap` for which applying the identity substitution is the identity. -/
  class SubstMapId (S T : Type) [RenMap T] [SubstMap S T] where
    /-- Applying the identity substitution leaves a value unchanged. -/
    apply_id {t : S} : t[+0:T] = t

  /-- A `SubstMap` whose substitution action agrees with renaming on renamings. -/
  class SubstMapStable (S : Type) [RenMap S] [SubstMap S S] where
    /-- Applying a renaming as a substitution agrees with applying it as a renaming. -/
    apply_stable (r : Ren) (σ : Subst S) : r = σ -> rmap (T := S) r = smap σ

  /-- A `SubstMap` for which renaming commutes with substitution. -/
  class SubstMapRenCommute (S T : Type) [RenMap S] [RenMap T] [SubstMap S T] where
    /-- Renaming after substituting equals substituting after renaming. -/
    apply_ren_commute {s : S} (r : Ren) (τ : Subst T) : s⟨r⟩[τ:T] = s[τ:T]⟨r⟩

  /-- A `SubstMap` for which a renaming followed by a substitution fuses on the left. -/
  class SubstMapRenComposeLeft (S T : Type) [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] where
    /-- Substituting by a renaming then by `τ` equals substituting by their composition. -/
    apply_ren_compose_left {s : S} {r : Ren} {τ : Subst T} : s[r.to:T][τ:_] = s[r.to ∘ τ:T]

  /-- A `SubstMap` for which a substitution followed by a renaming fuses on the right. -/
  class SubstMapRenComposeRight (S T : Type) [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] where
    /-- Substituting by `σ` then by a renaming equals substituting by their composition. -/
    apply_ren_compose_right {s : S} {r : Ren} {σ : Subst T} : s[σ:_][r.to:T] = s[σ ∘ r.to:T]

  /-- A `SubstMap` for which composed substitutions fuse. -/
  class SubstMapCompose (S T : Type) [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] where
    /-- Substituting by `σ` then by `τ` equals substituting by their composition. -/
    apply_compose {s : S} {σ τ : Subst T} : s[σ:T][τ:_] = s[σ ∘ τ:T]

  /-- A `SubstMap` for which heterogeneously composed substitutions fuse. -/
  class SubstMapHetCompose (S T : Type) [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] where
    /-- Substituting by `σ` then by `τ` equals substituting by their heterogeneous composition. -/
    apply_hcompose {s : S} {σ : Subst S} {τ : Subst T} : s[σ][τ:T] = s[τ:T][σ ◾ τ]

  namespace Subst
    export SubstMapStable (apply_stable)
    export SubstMapRenCommute (apply_ren_commute)
    export SubstMapRenComposeLeft (apply_ren_compose_left)
    export SubstMapRenComposeRight (apply_ren_compose_right)
  end Subst

  theorem Ren.lift_eq_from_eq [RenMap T] [SubstMap S T] {r : Ren} {σ : Subst T}
    : r = σ -> r.lift = σ.lift
  := by intro h; rw [<-h, to_lift]

  namespace Subst
    section
      @[simp, grind =]
      theorem rewrite1 : re 0 :: +1 = +0@T := by
        simp [Subst.cons, Subst.id]
        funext; case _ x =>
        cases x; all_goals simp

      open SubstMap
      variable [RenMap T]

      @[simp, grind =]
      theorem I_lift {k} : +0.lift k = +0@T := by
        funext; case _ x =>
        cases x; all_goals (simp [Subst.lift, Subst.id])
        grind

      omit [RenMap T] in
      @[simp, grind =]
      theorem rewrite2 [SubstMap T T] {σ : Subst T} : +0 ∘ σ = σ := by
        funext; case _ x =>
        unfold Subst.compose; simp [Subst.id]

      omit [RenMap T] in
      @[simp, grind =]
      theorem rewrite3_replace [SubstMap T T] {σ τ : Subst T} {s : T}
        : (su s :: σ) ∘ τ = su s[τ] :: (σ ∘ τ)
      := by
        simp [Subst.cons, Subst.compose]
        funext; case _ x =>
        cases x; all_goals simp

      omit [RenMap T] in
      @[simp, grind =]
      theorem rewrite3_rename [SubstMap T T] {s} {σ τ : Subst T}
        : (re s :: σ) ∘ τ = (τ.act s) :: (σ ∘ τ)
      := by
        simp [Subst.cons, Subst.compose]
        funext; case _ x =>
        cases x; all_goals simp

      omit [RenMap T] in
      @[simp, grind =]
      theorem rewrite4 [SubstMap T T]  {s} {σ : Subst T} : +1 ∘ (s :: σ) = σ := by
        simp [Subst.cons]
        funext; case _ x =>
        cases x; all_goals (simp [Subst.compose, Subst.succ])

      omit [RenMap T] in
      @[simp, grind =]
      theorem rewrite5 [SubstMap T T] {σ : Subst T} : σ.act 0 :: (+1 ∘ σ) = σ := by
        simp [Subst.cons, Subst.compose]; congr
        funext; case _ x =>
        cases x <;> simp
    end

    @[simp, grind =]
    theorem apply_I_is_id [RenMap T] [SubstMap S T] [SubstMapId S T] {s : S}
      : s[+0:T] = s
    := SubstMapId.apply_id

    @[simp, grind =]
    theorem rewrite_lift [RenMap T] [SubstMap T T] [SubstMapStable T] {σ : Subst T}
      : σ.lift = re 0 :: (σ ∘ +1)
    := by
      simp [Subst.cons, Subst.lift, Subst.compose]
      funext; case _ x =>
      cases x; simp
      case _ n =>
        simp [Subst.succ]
        generalize tdef : σ.act n = t
        cases t <;> simp at *
        case _ y =>
          rw [apply_stable (σ := +1)]
          simp [Subst.succ]
          rw [Ren.to_succ]

    @[simp, grind =]
    theorem rewrite_lift_zero [RenMap S] [RenMapId S] {σ : Subst S}
      : σ.lift 0 = σ
    := by
      simp [Subst.lift]; congr; funext; case _ i =>
      generalize zdef : σ.act i = z
      cases z <;> simp [Ren.add]; case _ s =>
      have lem := RenMapId.apply_id (t := s)
      simp [Ren.id] at lem; exact lem

    @[grind =]
    theorem rewrite_lift_succ
      [RenMap S] [RenMapId S] [RenMapCompose S]
      {k} {σ : Subst S}
      : σ.lift (k + 1) = (σ.lift k).lift
    := by
      induction k; simp
      case _ n ih =>
        replace ih i : (σ.lift (n + 1)).act i = ((σ.lift n).lift 1).act i := by rw [ih]
        simp [Subst.lift]
        funext; case _ i =>
        have lem := ih i
        cases i <;> simp
        case _ i =>
          simp [Subst.lift] at lem
          split; simp; case _ h1 =>
          simp at h1
          have lem2 : n ≤ i := by omega
          generalize zdef : σ.act (i - (n + 1)) = z
          cases z <;> simp; omega
          congr

    @[simp, grind =]
    theorem rewrite6 [RenMap T] [SubstMap T T] [SubstMapId T T] {σ : Subst T}
      : σ ∘ +0 = σ
    := by
      simp [Subst.compose, Subst.id]; congr
      funext; case _ x =>
      generalize zdef : σ.act x = z
      cases z <;> simp at *; case _ s =>
      have lem := SubstMapId.apply_id (T := T) (t := s)
      simp [Subst.id] at lem; exact lem

    @[simp, grind =]
    theorem apply_compose
      [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
      {s : S} {σ τ : Subst T}
      : s[σ:T][τ:_] = s[σ ∘ τ:T]
    := SubstMapCompose.apply_compose

    @[simp, grind =]
    theorem rewrite7
      [RenMap T] [SubstMap T T] [SubstMapCompose T T]
      {σ τ μ : Subst T}
      : (σ ∘ τ) ∘ μ = σ ∘ τ ∘ μ
    := by
      simp [Subst.compose]
      funext; case _ x =>
      cases σ.act x <;> simp [Subst.compose]

    @[simp, grind =]
    theorem hrewrite1
      [RenMap T] [SubstMap S T] [SubstMapId S T]
      {σ : Subst S}
      : σ ◾ (+0@T) = σ
    := by
      simp [Subst.hcompose]; congr
      funext; case _ x =>
      generalize zdef : σ.act x = z
      cases z <;> simp

    @[simp, grind =]
    theorem hcomp_ren_left
      [RenMap S] [RenMap T] [SubstMap S T]
      (r : Ren) (σ : Subst T)
      : (@Ren.to S r) ◾ σ = r.to
    := by
      funext; case _ x =>
      induction x <;> simp [Subst.hcompose, Ren.to]

    @[simp, grind =]
    theorem hrewrite2
      [RenMap S] [RenMap T] [SubstMap S T]
      {σ : Subst T}
      : (+0@S) ◾ σ = +0
    := by
      apply hcomp_ren_left (S := S) (T := T) Ren.id σ

    @[simp, grind =]
    theorem hrewrite3
      [RenMap S] [RenMap T] [SubstMap S T]
      {σ : Subst T}
      : (+1@S) ◾ σ = +1
    := by
      have lem := hcomp_ren_left (S := S) (T := T) (Ren.add 1) σ
      simp at lem; exact lem

    @[simp, grind =]
    theorem hrewrite4
      [RenMap T] [SubstMap S T]
      {x} {σ : Subst S} {τ : Subst T}
      : (re x :: σ) ◾ τ = re x :: (σ ◾ τ)
    := by
      simp [Subst.hcompose]; congr
      funext; case _ i =>
      cases i <;> simp [Subst.cons]

    @[grind =]
    theorem hcomp_dist_ren_left
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T]
      (r : Ren) {σ : Subst S} {τ : Subst T}
      : (r.to ∘ σ) ◾ τ = r.to ∘ σ ◾ τ
    := by
      funext; case _ x =>
      simp [Subst.hcompose, Subst.compose, Ren.to]

    @[simp, grind =]
    theorem hrewrite5
      [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
      {σ : Subst S} {τ μ : Subst T}
      : (σ ◾ τ) ◾ μ = σ ◾ (τ ∘ μ)
    := by
      simp [Subst.hcompose]
      funext; case _ x =>
      generalize zdef : σ.act x = z
      cases z <;> simp

    @[grind =]
    theorem hcomp_distr_ren_right
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T]
      [SubstMapStable S] [SubstMapRenCommute S T]
      (r : Ren) (σ : Subst S) (μ : Subst T)
      : (σ ∘ r.to) ◾ μ = (σ ◾ μ) ∘ r.to
    := by
      simp [Subst.hcompose, Subst.compose, Ren.to]
      funext; case _ x =>
      generalize zdef : σ.act x = z
      cases z <;> simp
      rw [<-apply_stable r ⟨λ n => re (r.act n)⟩ rfl]
      rw [SubstMapRenCommute.apply_ren_commute r μ]

    @[grind =]
    theorem hcomp_distr_ren_right_p1
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T]
      [SubstMapStable S] [SubstMapRenCommute S T]
      (σ : Subst S) (μ : Subst T)
      : (σ ∘ +1) ◾ μ = (σ ◾ μ) ∘ +1
    := by
      have lem : @Subst.succ S = Ren.to (Ren.add 1) := by simp
      rw [lem, hcomp_distr_ren_right]

    @[simp, grind =]
    theorem hrewrite6
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T]
      [SubstMapStable S] [SubstMapRenCommute S T]
      (r : Ren) (σ : Subst S)
      : (σ ∘ r.to) ◾ (+1@T) = (σ ◾ +1@T) ∘ r.to
    := by
      have lem := hcomp_distr_ren_right (T := T) r σ +1
      exact lem

    @[simp, grind =]
    theorem apply_hcompose
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
      {s : S} {σ : Subst S} {τ : Subst T}
      : s[σ][τ:T] = s[τ:T][σ ◾ τ]
    := by exact SubstMapHetCompose.apply_hcompose

    @[simp, grind =]
    theorem hrewrite7
      [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T] [SubstMapHetCompose S T]
      {σ τ : Subst S} (μ : Subst T)
      : (σ ∘ τ) ◾ μ = (σ ◾ μ) ∘ τ ◾ μ
    := by
      simp [Subst.hcompose, Subst.compose]
      funext; case _ x =>
      generalize zdef : σ.act x = z
      cases z <;> simp [Subst.hcompose]

    theorem hrewrite_lift1
      [RenMap S] [RenMap T] [SubstMap S T] [SubstMapRenCommute S T]
      {σ : Subst S} {τ : Subst T}
      : (σ ◾ τ).lift = σ.lift ◾ τ
    := by
      simp [Subst.lift]; congr; funext; case _ i =>
      cases i <;> simp [hcompose]
      case _ n =>
        generalize zdef : σ.act n = z
        cases z <;> simp; case _ t =>
        rw [SubstMapRenCommute.apply_ren_commute]

    @[simp, grind =]
    theorem hrewrite_lift
      [RenMap S] [RenMap T] [SubstMap S T] [RenMapId S] [RenMapCompose S] [SubstMapRenCommute S T]
      {k} {σ : Subst S} {τ : Subst T}
      : (σ ◾ τ).lift k = σ.lift k ◾ τ
    := by
      induction k generalizing σ τ
      case _ => simp
      case _ i ih =>
        rw [rewrite_lift_succ]
        rw [rewrite_lift_succ]
        simp; rw [ih, hrewrite_lift1]
        grind
  end Subst

  @[grind =]
  theorem Subst.Compose.lemma1
    [RenMap S] [SubstMap S S] [RenMapId S] [RenMapCompose S] [SubstMapStable S]
    {k} {τ : Subst S}
    : (Ren.to (Ren.add 1)) ∘ τ.lift (k + 1) = τ.lift k ∘ (Ren.to (Ren.add 1))
  := by
    simp [Subst.compose]
    funext; case _ x =>
    cases x
    all_goals
      unfold Subst.lift; simp
      split; simp; split
    any_goals solve | congr 1
    all_goals
      rw [<-apply_stable _ +1 rfl]
      simp; congr

  @[grind =]
  theorem Subst.Compose.lemma1s
    [RenMap S] [SubstMap S S] [RenMapId S] [RenMapCompose S] [SubstMapStable S]
    {k} {τ : Subst S}
    : +1 ∘ τ.lift (k + 1) = τ.lift k ∘ +1
  := by
    have lem : @Subst.succ S = Ren.to (Ren.add 1) := by simp
    rw [lem]; grind

  @[grind =]
  theorem Subst.Compose.lemma2_k1
    [RenMap S] [SubstMap S S] [RenMapId S] [RenMapCompose S]
    {σ : Subst S} {r : Ren}
    : (r ∘ σ).lift = (Ren.to r).lift ∘ σ.lift
  := by
    simp [Subst.lift, Subst.compose, Ren.to]
    funext; case _ x =>
    cases x <;> simp

  @[grind =]
  theorem Subst.Compose.lemma2
    [RenMap S] [SubstMap S S] [RenMapId S] [RenMapCompose S]
    {k} {σ : Subst S} {r : Ren}
    : (r ∘ σ).lift k = (Ren.to r).lift k ∘ σ.lift k
  := by
    induction k generalizing r σ; simp
    case _ k ih =>
    rw [Subst.rewrite_lift_succ, ih]
    rw [<-Ren.to_lift, Subst.Compose.lemma2_k1]
    rw [Subst.rewrite_lift_succ (σ := r.to)]
    rw [Subst.rewrite_lift_succ (σ := σ)]
    grind

  @[grind =]
  theorem Subst.Compose.lemma2s
    [RenMap S] [SubstMap S S] [RenMapId S] [RenMapCompose S]
    {k} {σ : Subst S}
    : (+1 ∘ σ).lift k = +1.lift k ∘ σ.lift k
  := by
    have lem : @Subst.succ S = Ren.to (Ren.add 1) := by simp
    rw [lem]; grind

  @[grind =]
  theorem Subst.Compose.lemma3
    [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapRenComposeLeft S T]
    {s : S} {σ : Subst T}
    : s[+1:T][σ:_] = s[+1 ∘ σ:_]
  := by
    have lem : @Subst.succ T = Ren.to (Ren.add 1) := by simp
    rw [lem, apply_ren_compose_left]

  @[grind =]
  theorem Subst.Compose.lemma4
    [RenMap T] [SubstMap T T]
    {σ τ : Subst T}
    : +1 ∘ τ ∘ σ = (+1 ∘ τ) ∘ σ
  := by
    funext; case _ x =>
    cases x <;> simp [Subst.compose, Subst.succ]

  @[grind =]
  theorem Subst.compose.lemma5
    [RenMap T] [SubstMap T T] [RenMapCompose T] [SubstMapStable T]
    {r1 r2 : Ren} {τ : Subst T}
    : (τ ∘ r2.to) ∘ r1.to = τ ∘ r2.to ∘ r1.to
  := by
    simp [Subst.compose]
    funext; case _ x =>
    cases τ.act x <;> simp [*]
    simp [Ren.to]
    rw [<-apply_stable r2 ⟨λ n => re (r2.act n)⟩ rfl]
    rw [<-apply_stable r1 ⟨λ n => re (r1.act n)⟩ rfl]
    simp
    rw [apply_stable _ _ rfl]
    rw [Ren.to_compose]
    unfold Subst.compose; simp [Ren.to]

  @[grind =]
  theorem Subst.Compose.lemma6_k1
    [RenMap S] [SubstMap S S] [SubstMapStable S] [SubstMapRenComposeLeft S S]
    {σ : Subst S} {r : Ren}
    : (σ ∘ r.to).lift = σ.lift ∘ (Ren.to r).lift
  := by
    simp [Subst.lift, Subst.compose]
    funext; case _ x =>
    cases x <;> simp
    case _ x =>
      cases σ.act x <;> simp
      rw [apply_stable (Ren.add 1) _ rfl]
      rw [apply_ren_compose_left]
      rw [apply_ren_compose_left]
      simp [Ren.to, Subst.compose, Ren.add]

  @[grind =]
  theorem Subst.Compose.lemma6
    [RenMap S] [SubstMap S S] [RenMapId S] [RenMapCompose S]
    [SubstMapStable S] [SubstMapRenComposeLeft S S]
    {k} {σ : Subst S} {r : Ren}
    : (σ ∘ r.to).lift k = σ.lift k ∘ (Ren.to r).lift k
  := by
    induction k generalizing r σ; simp
    case _ k ih =>
    rw [Subst.rewrite_lift_succ, ih]
    rw [<-Ren.to_lift, Subst.Compose.lemma6_k1]
    rw [Subst.rewrite_lift_succ (σ := r.to)]
    rw [Subst.rewrite_lift_succ (σ := σ)]
    grind

  @[grind =]
  theorem Subst.Compose.lemma6s
    [RenMap S] [SubstMap S S] [RenMapId S] [RenMapCompose S]
    [SubstMapStable S] [SubstMapRenComposeLeft S S]
    {k} {σ : Subst S}
    : (σ ∘ +1).lift k = σ.lift k ∘ +1.lift k
  := by
    have lem : @Subst.succ S = Ren.to (Ren.add 1) := by simp
    rw [lem]; grind

  @[grind =]
  theorem Subst.Compose.lemma7
    [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapRenComposeRight S T]
    {s : S} {τ : Subst T}
    : s[τ:_][+1:T] = s[τ ∘ +1:_]
  := by
    have lem : @Subst.succ T = Ren.to (Ren.add 1) := by simp
    rw [lem, apply_ren_compose_right]

  @[grind =]
  theorem Subst.Compose.lemma8
    [RenMap T] [SubstMap T T] [SubstMapRenComposeLeft T T]
    {σ τ : Subst T}
    : (σ ∘ +1) ∘ τ = σ ∘ +1 ∘ τ
  := by
    simp [Subst.compose]
    funext; case _ x =>
    cases σ.act x <;> simp at *
    rw [lemma3]
    unfold Subst.compose; simp

  @[grind =]
  theorem Subst.Compose.lemma9
    [RenMap T] [SubstMap T T] [SubstMapRenComposeRight T T]
    {σ τ : Subst T}
    : ((σ ∘ τ) ∘ +1) = σ ∘ τ ∘ +1
  := by
    simp [Subst.compose]
    funext; case _ x =>
    cases σ.act x <;> simp at *
    rw [lemma7]
    unfold Subst.compose; simp

  @[grind =]
  theorem Subst.Compose.lemma10
    [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T]
    [SubstMapStable S] [SubstMapRenCommute S T]
    {σ : Subst S} {μ : Subst T} {r : Ren}
    : (σ ∘ r.to) ◾ μ = (σ ◾ μ) ∘ r.to
  := by
    simp [Subst.hcompose, Subst.compose]
    funext; case _ x =>
    generalize zdef : σ.act x = z
    cases z <;> simp [Ren.to]
    rw [<-apply_stable r ⟨λ n => re (r.act n)⟩ rfl]
    rw [Subst.apply_ren_commute]

  @[grind =]
  theorem Subst.Compose.lemma10s
    [RenMap S] [RenMap T] [SubstMap S S] [SubstMap S T]
    [SubstMapStable S] [SubstMapRenCommute S T]
    {σ : Subst S} {μ : Subst T}
    : (σ ∘ +1) ◾ μ = (σ ◾ μ) ∘ +1
  := by
    have lem := lemma10 (σ := σ) (μ := μ) (r := (Ren.add 1))
    simp at lem; exact lem

  theorem Subst.rewrite_lift_compose_k1
    [RenMap T] [SubstMap T T] [SubstMapStable T]
    [SubstMapRenComposeLeft T T] [SubstMapRenComposeRight T T]
    {σ τ : Subst T}
    : (σ ∘ τ).lift = σ.lift ∘ τ.lift
  := by
    simp [Subst.lift, Subst.compose]
    funext; case _ x =>
    cases x <;> simp
    case _ x =>
    cases σ.act x <;> simp
    rw [apply_stable _ (Ren.add 1) rfl]; simp
    rw [Compose.lemma7, Compose.lemma3]
    simp [Subst.compose]

  @[simp, grind =]
  theorem Subst.rewrite_lift_compose
    [RenMap T] [SubstMap T T] [RenMapId T] [RenMapCompose T] [SubstMapStable T]
    [SubstMapRenComposeLeft T T] [SubstMapRenComposeRight T T]
    {k} {σ τ : Subst T}
    : (σ ∘ τ).lift k = σ.lift k ∘ τ.lift k
  := by
    induction k generalizing σ τ; simp
    case _ k ih =>
      rw [rewrite_lift_succ, ih]
      rw [rewrite_lift_succ (σ := σ)]
      rw [rewrite_lift_succ (σ := τ)]
      rw [rewrite_lift_compose_k1]

  /-- Tactic that discharges a `SubstMapId.apply_id` obligation by induction on the term. -/
  macro "substSolveId" : tactic => `(tactic| {
    intro t; induction t
    any_goals solve | simp +instances [*]
    all_goals try simp at *; simp  +instances [*]; grind
  })

  /-- Tactic that discharges a `SubstMapStable.apply_stable` obligation by induction on the term. -/
  macro "substSolveStable" : tactic => `(tactic| {
    intro r σ h
    funext; case _ t =>
    induction t generalizing r σ
    all_goals simp [rmap, smap, *] at *; try simp +instances [*]
    any_goals solve | (rw [<-h]; simp +instances [Ren.to])
    all_goals try repeat funext; grind
  })

  /-- Tactic that discharges a `SubstMapCompose.apply_compose` obligation by induction on the term. -/
  macro "substSolveCompose" : tactic => `(tactic| {
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift, *]
      try grind)
  })

end LeanSubst
