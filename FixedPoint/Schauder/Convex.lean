/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Common.SchauderProjection
public import FixedPoint.Brouwer.Polytope
public import FixedPoint.Common.ContinuousMap

/-!
# Schauder's fixed-point theorem for compact convex sets

* `Schauder.exists_dist_lt`: for every `ε > 0`, a continuous self-map `f` of a nonempty compact
  convex set `s` of a real normed space moves some point of `s` by less than `ε`.
* `Schauder.exists_fixedPoint` (**Schauder's fixed-point theorem**, J. Schauder, *Der Fixpunktsatz
  in Funktionalräumen*, Studia Math. 2 (1930), 171–180, Satz I): `f` has a fixed point in `s`.
* `Schauder.exists_fixedPoint_continuousMap`: the same for a continuous map `C(s, s)`.

## Proof

Cover `s` by finitely many open balls of radius `ε` centered at the points of a finite set
`t ⊆ s`, and let `P` be Schauder's projection onto the convex hull `K ⊆ s` of `t`
(`SchauderProjection.blend`), which moves each point of `s` by less than `ε`. The map `P ∘ f`
sends `K` continuously into itself, and `K` lies in the finite-dimensional span of `t`, so
it has a fixed point `x` (`Brouwer.exists_fixedPoint_convexHull_of_finite`). Then
`dist (f x) x = dist (f x) (P (f x)) < ε`. With `ε = 1 / (n + 1)` this gives points `x n ∈ s`
with `dist (f (x n)) (x n) → 0`; a subsequence converges to some `x ∈ s`, and `f x = x` by
continuity.

Schauder's proof has the same structure: a finite `ε`-net, Brouwer's theorem on its convex hull,
a point that `f` moves by little, and compactness. Departure from Schauder's proof: Schauder
triangulates the convex hull of the net finely and approximates `f` there by a simplicial map that
sends each vertex `d` to a point of the net within `ε` of `f d`; the formalization uses the
projection `P` above, the "Schauder projection" of later expositions, which is not in the paper.
Reason: Mathlib has no triangulations of polytopes or simplicial approximation. The convexity of
balls replaces Schauder's Hilfssatz I, whose `δ(n, ε)` is `ε` in a normed space.

Statement: Schauder states Satz I for complete metric linear spaces, not necessarily locally
convex; his proof uses convexity of balls there and is valid only for normed (or locally convex)
spaces, and the general case is Schauder's problem (Scottish Book, Problem 54). The theorem is
stated here for real normed spaces, complete or not.
-/

@[expose] public section

open Set Filter Topology

namespace Schauder

open SchauderProjection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For every `ε > 0`, a map that is continuous on a nonempty compact convex set `s` of a real
normed space and maps `s` into itself moves some point of `s` by less than `ε`. -/
theorem exists_dist_lt {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)
    {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ s, dist (f x) x < ε := by
  obtain ⟨t, hts, hcov⟩ := exists_finset_cover hcomp hε
  have htne : (t : Set E).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨c, hc, -⟩ := hcov x hx
    exact ⟨c, hc⟩
  have hK : convexHull ℝ (t : Set E) ⊆ s := convexHull_min hts hconv
  -- Schauder's projection onto the convex hull of `t`
  let P := blend t ε id
  obtain ⟨x, hx, hPx⟩ := Brouwer.exists_fixedPoint_convexHull_of_finite t.finite_toSet htne
    (f := P ∘ f) (fun x hx ↦ blend_id_mem_convexHull (hcov _ (hmaps (hK hx))))
    ((continuousOn_blend _ ε id).comp (hf.mono hK) fun x hx ↦ hcov _ (hmaps (hK hx)))
  refine ⟨x, hK hx, ?_⟩
  have hlt := dist_blend_id_lt (hcov _ (hmaps (hK hx)))
  rw [show blend t ε id (f x) = x from hPx, dist_comm] at hlt
  exact hlt

/-- **Schauder's fixed-point theorem**: in a real normed space, a map that is continuous on a
nonempty compact convex set `s` and maps `s` into itself has a fixed point in `s`. -/
theorem exists_fixedPoint {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x := by
  choose x hxs hx using fun n : ℕ ↦
    exists_dist_lt hconv hcomp hne hmaps hf (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  obtain ⟨a, has, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hxs
  have hfa : Tendsto (fun k ↦ f (x (φ k))) atTop (𝓝 (f a)) :=
    (hf a has).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k ↦ hxs _⟩)
  have hdist : Tendsto (fun k ↦ dist (f (x (φ k))) (x (φ k))) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hx (φ k)).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  exact ⟨a, has, dist_le_zero.1 (le_of_eq (tendsto_nhds_unique (hfa.dist hlim) hdist))⟩

/-- **Schauder's fixed-point theorem** for a continuous self-map of a nonempty compact convex set
of a real normed space. -/
theorem exists_fixedPoint_continuousMap {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x :=
  FixedPoint.exists_fixedPoint_continuousMap_of
    (fun _ hmaps hf ↦ exists_fixedPoint hconv hcomp hne hmaps hf) f

end Schauder
