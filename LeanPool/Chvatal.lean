/-
Copyright (c) 2026 Chvatal formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chvatal formalization contributors
-/
module

public import LeanPool.Chvatal.Main
public import LeanPool.Chvatal.Sharpness
public import LeanPool.Chvatal.Weighted
public import LeanPool.Chvatal.Signed

/-!
# Chvátal's conjecture and sharp Boolean correlation

Source: arxiv:2609.19123v1, url:https://github.com/boonsuan/chvatal
Authors: Boon Suan Ho, Chvatal formalization contributors
Status: verified
Main declarations: `Chvatal.chvatal`, `Chvatal.sharp_correlation`
Tags: extremal-combinatorics, intersecting-families, Fourier-analysis
MSC: 05D05, 60E15
-/

@[expose] public section

/-
Upstream: https://github.com/boonsuan/chvatal
Commit: c19ed3aaac9e42d446f963a862d39d8a09eddbf9
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Chvatal formalization contributors

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

/-
# A proof of Chvátal's conjecture via a sharp correlation inequality

Public entry point for the formalization of Chang–Liu–Liu, arXiv:2609.19123v1.
Upstream docs/PaperMap.md at the recorded commit maps all numbered paper results.
This import retains the complete mathematical module closure.
-/
