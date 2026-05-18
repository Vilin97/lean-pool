/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/

import Mathlib.CategoryTheory.Category.Basic

register_label_attr zrel
register_label_attr zpfun
register_label_attr zfun

/-!
Thanks to Ghilain for the idea of registering specific attributes
-/
namespace ZFTactics
set_option hygiene false

macro "zrel" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zrel, zpfun, zfun)

macro "zpfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zpfun, zfun)

macro "zfun" : tactic => `(tactic|
  first
  | sorry_if_sorry
  | solve_by_elim using zfun)
end ZFTactics
