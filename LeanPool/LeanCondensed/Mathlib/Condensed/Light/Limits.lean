/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Light.Functors
import Mathlib.Condensed.Light.Module

/-!
# Limits in categories of light condensed objects

This file adds some instances for limits in light condensed sets and modules.
-/

universe u

open CategoryTheory Limits

instance : HasLimitsOfSize.{u, u} LightCondSet.{u} :=
  inferInstanceAs <| HasLimitsOfSize (Sheaf _ _)

instance : HasFiniteLimits LightCondSet.{u} := hasFiniteLimits_of_hasLimitsOfSize _

noncomputable instance {I : Type*} [Category I] (K : I ⥤ LightProfinite.{u}) :
    PreservesLimit K lightProfiniteToLightCondSet where
  preserves hc := ⟨isLimitOfReflects (sheafToPresheaf _ _) (isLimitOfPreserves yoneda hc)⟩

noncomputable instance : PreservesLimits lightProfiniteToLightCondSet where
  preservesLimitsOfShape := { preservesLimit := inferInstance }

variable (R : Type u) [Ring R]

instance : HasLimitsOfSize.{u, u} (LightCondMod.{u} R) := by
  change HasLimitsOfSize (Sheaf _ _)
  infer_instance

instance : HasFiniteLimits (LightCondMod.{u} R) := hasFiniteLimits_of_hasLimitsOfSize _
