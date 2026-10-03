/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N3TruthTable
public import LeanPool.BooleanMultiplication.N4.Main

/-!
# Exact Boolean multiplicative complexity of four-term polynomial multiplication

Source: arxiv:2608.30238v1, url:https://github.com/GregoryMorse/unrestricted-boolean-mul/tree/79a801760668f52bb00a9e1a406e841375c58a6d
Authors: Gregory Morse
Status: verified
Main declarations: `UnrestrictedBooleanMul.N4.mc_mul_four`
Tags: computational-complexity, boolean-circuits, polynomial-multiplication, algebraic-normal-form
MSC: 68Q06, 68Q17, 68W30, 15A75, 94D10
-/

/-!
The circuit model allows arbitrary reuse of earlier nonlinear wires, with XOR and constants free.
The exact values for input lengths zero through four are proved internally. General infrastructure
includes Boolean ANFs, circuit dimension bounds and rewiring, and Reed–Muller weight bounds.

This imports the published four-term result from Gregory Morse's MIT-licensed repository. The
August 31, 2026 Lean release establishes eligibility; the pinned September revision ports and
packages the same result. The author discloses an AI proof-development workflow under his direction
and review. The project card records AI provenance and the source details. The upstream license
notice is retained below.
-/

public section

/-
MIT License

Copyright (c) 2026 Gregory Morse

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
