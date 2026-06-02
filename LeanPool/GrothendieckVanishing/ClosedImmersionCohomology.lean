/-
Copyright (c) 2026 Vasily Ilin, Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Brian Nugent
-/

import LeanPool.GrothendieckVanishing.ClosedImmersion
import LeanPool.GrothendieckVanishing.CohomologyAPI
import LeanPool.GrothendieckVanishing.FlasqueVanishing

/-!
# Closed-immersion cohomology

Cohomological consequences of closed inclusions used in the Grothendieck vanishing proof.

## Main results

* `PushforwardHIso` — pushforward along a closed inclusion preserves sheaf cohomology, as
  an isomorphism in every degree.
* `subsingleton_sheafH_of_closedImmersion_middle` — vanishing of `Hⁿ` of the middle term in
  the closed-immersion short exact sequence, given vanishing for the kernel and the pullback.

The closed-inclusion stalk, exactness, and adjunction-unit short exact sequence API live
in `ClosedImmersion.lean`. LES-facing `Sheaf.H` wrappers come from `CohomologyAPI.lean`,
and the flasque infrastructure from `FlasqueVanishing.lean`.
-/

universe u

open CategoryTheory TopologicalSpace Abelian Limits Opposite

/-! ## Closed-immersion cohomology consequences -/

/-- Pushforward along a closed inclusion preserves sheaf cohomology in every degree, as an
isomorphism. The proof is by induction: in degree zero via sections, in degree one via the
cokernel model of `H¹`, and in higher degrees via dimension-shift isomorphisms on both
sides combined with the induction hypothesis on the next term of an injective resolution. -/
noncomputable def PushforwardHIso
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of Z))
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H G n) ≅
      AddCommGrpCat.of (Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.closedIncl hZ)).obj G) n) := by
  let closedIncl := TopCat.closedIncl hZ
  induction n generalizing G with
  | zero =>
    exact by
      change (sheafCohomologyFunctor (TopCat.of Z) 0).obj G ≅
        (sheafCohomologyFunctor X 0).obj
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj G)
      simpa [Opens.map_top] using
        (sheafH0NatIsoSections (X := TopCat.of Z)).app G ≪≫
          ((sheafH0NatIsoSections (X := X)).app
            ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj G)).symm
  | succ k ih_push =>
    classical
    let ip : InjectivePresentation G := Classical.choice (EnoughInjectives.presentation G)
    let S := ip.shortComplex
    let SX := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl)
    have hSE_X : SX.ShortExact :=
      closedIncl_pushforward_shortExact hZ ip.shortExact_shortComplex
    have hFlasqueSX₂ : IsFlasqueSheaf SX.X₂ := fun j ↦ by
      change Epi (S.X₂.obj.map ((Opens.map closedIncl).op.map j.op))
      exact (isFlasque_of_injective S.X₂) ((Opens.map closedIncl).map j)
    have hSE : S.ShortExact := by simpa [S] using ip.shortExact_shortComplex
    have hSrcSub (r : ℕ) : Subsingleton (Sheaf.H S.X₂ (r + 1)) :=
      sheafH_subsingleton_of_injective S.X₂ r
    have hTgtSub (r : ℕ) : Subsingleton (Sheaf.H SX.X₂ (r + 1)) :=
      sheafH_subsingleton_of_flasque X SX.X₂ hFlasqueSX₂ r
    change AddCommGrpCat.of (Sheaf.H G (k + 1)) ≅
      AddCommGrpCat.of (Sheaf.H SX.X₁ (k + 1))
    cases k with
    | zero =>
      exact by
        simpa [S, SX] using
          (show cokernel (SX.g.hom.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H G 1) from by
            change cokernel (S.g.hom.app (op ⊤)) ≅ AddCommGrpCat.of (Sheaf.H S.X₁ 1)
            exact sheafH1CokernelIsoOfSubsingletonMiddle hSE (hSrcSub 0)).symm ≪≫
          sheafH1CokernelIsoOfSubsingletonMiddle hSE_X (hTgtSub 0)
    | succ m =>
      exact by
        simpa [S, SX] using
          (sheafHSuccIsoOfSubsingletonMiddle hSE (m + 1) (hSrcSub m)
            (hSrcSub (m + 1))).symm ≪≫
        ih_push S.X₃ ≪≫
          sheafHSuccIsoOfSubsingletonMiddle hSE_X (m + 1) (hTgtSub m)
            (hTgtSub (m + 1))

/-- Closed-immersion step: if the kernel term of the closed-immersion
short exact sequence and the pullback to the closed subset have subsingleton
cohomology in degree `n`, then so does the ambient sheaf. -/
theorem subsingleton_sheafH_of_closedImmersion_middle
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (h₁ : Subsingleton
      (Sheaf.H ((closedImmersionSES (Z := Z) (hZ := hZ) F).X₁) n))
    (h₃ : Subsingleton
      (Sheaf.H
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.closedIncl hZ)).obj
          F) n)) :
    Subsingleton (Sheaf.H F n) := by
  let closedIncl := TopCat.closedIncl hZ
  let FZ := ((TopCat.Sheaf.pullback AddCommGrpCat.{u} closedIncl).obj F)
  let S := closedImmersionSES (Z := Z) (hZ := hZ) F
  have hSE := closedImmersionSES_shortExact (Z := Z) (hZ := hZ) F
  have h₁' : Subsingleton (Sheaf.H S.X₁ n) := by
    simpa [S] using h₁
  have h₃' : Subsingleton (Sheaf.H FZ n) := by
    simpa [closedIncl, FZ] using h₃
  have hPush : Subsingleton (Sheaf.H S.X₃ n) := by
    let e :
        Sheaf.H FZ n ≃
          Sheaf.H ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} closedIncl).obj FZ) n :=
      Equiv.ofBijective (ConcreteCategory.hom (PushforwardHIso Z hZ FZ n).hom)
        (ConcreteCategory.bijective_of_isIso (PushforwardHIso Z hZ FZ n).hom)
    simpa [S, closedImmersionSES, closedIncl, FZ] using
      (e.subsingleton_congr).mp h₃'
  haveI : Mono S.f := hSE.mono_f
  have hCok : Subsingleton (Sheaf.H (cokernel S.f) n) := by
    let hSgCok : IsColimit (CokernelCofork.ofπ S.g S.zero) := hSE.gIsCokernel
    let e :=
      (sheafCohomologyFunctor X n).mapIso
        ((cokernelIsCokernel S.f).coconePointUniqueUpToIso hSgCok)
    haveI :
        Subsingleton ↑((sheafCohomologyFunctor X n).obj
          (CokernelCofork.ofπ S.g S.zero).pt) := by
      change Subsingleton (Sheaf.H S.X₃ n)
      exact hPush
    exact ⟨fun a b ↦ by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      exact Subsingleton.elim _ _⟩
  change Subsingleton (Sheaf.H S.X₂ n)
  exact subsingleton_sheafH_of_shortExact_middle S.f n h₁' hCok
