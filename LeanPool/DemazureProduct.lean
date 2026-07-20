/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import LeanPool.DemazureProduct.Utils
import LeanPool.DemazureProduct.Valley
import LeanPool.DemazureProduct.SlipFace
import LeanPool.DemazureProduct.AspPerm
import LeanPool.DemazureProduct.Submodular
import LeanPool.DemazureProduct.ReducedProducts
import LeanPool.DemazureProduct.Reduction
import LeanPool.DemazureProduct.Transpositions
import LeanPool.DemazureProduct.InvSet
import LeanPool.DemazureProduct.Avoiding321
import LeanPool.DemazureProduct.Tableaux

/-!
# Extended Demazure Product on ASP Permutations

Source: arxiv:2206.14227
Authors: Nathan Pflueger
Status: verified
Main declarations: `LeanPool.DemazureProduct.AspPerm.star`
Tags: algebraic-combinatorics, demazure-product, bruhat-order, permutations
MSC: 05E05, 20F55
-/

/-!
This project formalizes the extended Demazure product on almost-sign-preserving
integer permutations via min-plus matrix multiplication. The imported upstream
declarations are placed under `LeanPool.DemazureProduct` to avoid collisions
with the separate Demazure-operators project already in Lean Pool.
-/
