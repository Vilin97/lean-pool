/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic

namespace SPG.Algebra

/--
Generate the group closure from a list of generators.
This uses a fixed-point iteration: repeatedly adding all pairwise products
until the set size stabilizes.
-/
partial def generate_group (gens : List SPGElement) : List SPGElement :=
  let rec loop (current : List SPGElement) : List SPGElement :=
    let new_elements := (
      current.flatMap fun g1 =>
      current.flatMap fun g2 =>
      [g1 * g2]
    ).eraseDups
    let combined := (current ++ new_elements).eraseDups
    if combined.length == current.length then
      current
    else
      loop combined
  loop gens

def combine_generators (gens₁ gens₂ : List SPGElement) : List SPGElement :=
  generate_group (gens₁ ++ gens₂)

end SPG.Algebra
