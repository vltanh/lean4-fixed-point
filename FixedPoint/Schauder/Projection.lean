/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Brouwer.Polytope
public import FixedPoint.Common.SchauderProjection
public import FixedPoint.Schauder.Limit

/-!
# Schauder's theorem through Schauder's projection

A second proof of Schauder's fixed-point theorem for compact convex sets,
`Schauder.Projection.exists_fixedPoint`, with the same statement as `Schauder.exists_fixedPoint`.
Schauder's proof (`FixedPoint/Schauder/Convex.lean`) approximates `f` by a simplicial map; this one
by Schauder's projection, as in later expositions.

* `Schauder.Projection.exists_dist_lt`: cover `s` by finitely many open balls of radius `ε`
  centered at the points of a finite set `t ⊆ s`, and let `P` be Schauder's projection onto the
  convex hull `K ⊆ s` of `t` (`SchauderProjection.blend`), which moves each point of `s` by less
  than `ε`. The map `P ∘ f` sends `K` continuously into itself, and `K` lies in the
  finite-dimensional span of `t`, so it has a fixed point `x`
  (`Brouwer.exists_fixedPoint_convexHull_of_finite`). Then
  `dist (f x) x = dist (f x) (P (f x)) < ε`.
* `Schauder.Projection.exists_fixedPoint`: compactness, as in Schauder's proof
  (`Schauder.exists_fixedPoint_of_forall_dist_lt`).
-/

@[expose] public section

open Set Filter Topology

namespace Schauder.Projection

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

/-- **Schauder's fixed-point theorem**, proved through Schauder's projection: in a real normed
space, a map that is continuous on a nonempty compact convex set `s` and maps `s` into itself has a
fixed point in `s`. -/
theorem exists_fixedPoint {s : Set E} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : E → E} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x :=
  exists_fixedPoint_of_forall_dist_lt hcomp hf fun _ hε ↦
    exists_dist_lt hconv hcomp hne hmaps hf hε

end Schauder.Projection
