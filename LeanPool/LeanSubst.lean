/-
Copyright (c) 2026 Andrew Marmaduke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Marmaduke
-/
import LeanPool.LeanSubst.Ren
import LeanPool.LeanSubst.HetRen
import LeanPool.LeanSubst.Subst
import LeanPool.LeanSubst.Laws
import LeanPool.LeanSubst.Option
import LeanPool.LeanSubst.List
import LeanPool.LeanSubst.Reduction
import LeanPool.LeanSubst.Normal

/-!
# De Bruijn substitution framework (lean-subst)

Source: url:https://github.com/amarmaduke/lean-subst
Authors: Andrew Marmaduke
Status: verified
Main declarations: `LeanSubst.Subst.compose`, `LeanSubst.Ren.apply_compose`, `LeanSubst.Star.confluence`, `LeanSubst.Conv.star_equiv`, `LeanSubst.SN.wellfounded`
Tags: type-theory, de-bruijn, substitution, autosubst, rewriting
MSC: 03B40, 68N18
-/

/-!
## Overview

An Autosubst-style framework for De Bruijn substitution over non-indexed syntax.
Substitutions are modelled as sequences of substitution actions (`Subst.Action`),
so renamings embed into substitutions and variable-annotated data is preserved.
The development establishes the convergent rewriting laws of the substitution
calculus and uses them to prove abstract metatheory: confluence of reduction
relations and strong normalization.
-/
