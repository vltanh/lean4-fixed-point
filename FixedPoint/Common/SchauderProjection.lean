/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Schauder's projection

Let `t` be a finite set of points of a metric space `X` and `ε > 0`. The point `c ∈ t` has the
weight `max 0 (ε - dist x c)` at `x`, positive exactly on the open ball of radius `ε` about `c`.
On the union of these balls the weights do not all vanish, and the weighted average of values
`y c` in a real normed space,
`SchauderProjection.blend t ε y x = (∑ c ∈ t, weight c x)⁻¹ • ∑ c ∈ t, weight c x • y c`,

* is continuous (`SchauderProjection.continuousOn_blend`);
* is a convex combination of the values `y c` at the centers `c` within `ε` of `x`
  (`SchauderProjection.blend_mem_convexHull`).

For `y = id` this is Schauder's projection onto the convex hull of `t`, which moves each point of
the union of the balls by less than `ε` (`SchauderProjection.dist_blend_id_lt`). The name is the
one of later expositions: Schauder's 1930 paper approximates by simplicial maps instead.

A compact set is covered by such balls, about the points of a finite subset `t`
(`SchauderProjection.exists_finset_cover`).
-/

@[expose] public section

open Set Metric

namespace SchauderProjection

variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact set is covered by the open balls of radius `ε` about the points of a finite
subset. -/
theorem exists_finset_cover {s : Set X} (hs : IsCompact s) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset X, (t : Set X) ⊆ s ∧ ∀ x ∈ s, ∃ c ∈ t, dist x c < ε := by
  obtain ⟨t, hts, htfin, hcover⟩ := hs.finite_cover_balls hε
  refine ⟨htfin.toFinset, by simpa using hts, fun x hx ↦ ?_⟩
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcover hx)
  exact ⟨c, htfin.mem_toFinset.2 hc, hxc⟩

/-- The weight of the center `c` at `x`: positive exactly on the open ball of radius `ε` about
`c`. -/
noncomputable def weight (ε : ℝ) (c x : X) : ℝ := max 0 (ε - dist x c)

theorem weight_nonneg (ε : ℝ) (c x : X) : 0 ≤ weight ε c x := le_max_left _ _

theorem weight_pos_iff {ε : ℝ} {c x : X} : 0 < weight ε c x ↔ dist x c < ε := by
  simp [weight, lt_max_iff, sub_pos]

theorem continuous_weight (ε : ℝ) (c : X) : Continuous (weight ε c) :=
  continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))

/-- The average of the values `y c`, `c ∈ t`, weighted by `weight ε c x`. -/
noncomputable def blend (t : Finset X) (ε : ℝ) (y : X → E) (x : X) : E :=
  t.centerMass (fun c ↦ weight ε c x) y

theorem sum_weight_pos {t : Finset X} {ε : ℝ} {x : X} (hx : ∃ c ∈ t, dist x c < ε) :
    0 < ∑ c ∈ t, weight ε c x := by
  obtain ⟨c, hc, hxc⟩ := hx
  exact Finset.sum_pos' (fun c _ ↦ weight_nonneg ε c x) ⟨c, hc, weight_pos_iff.2 hxc⟩

/-- The weighted average is continuous on the union of the balls of radius `ε` about the points
of `t`. -/
theorem continuousOn_blend (t : Finset X) (ε : ℝ) (y : X → E) :
    ContinuousOn (blend t ε y) {x | ∃ c ∈ t, dist x c < ε} := by
  have hden : Continuous fun x ↦ ∑ c ∈ t, weight ε c x :=
    continuous_finsetSum _ fun c _ ↦ continuous_weight ε c
  have hnum : Continuous fun x ↦ ∑ c ∈ t, weight ε c x • y c :=
    continuous_finsetSum _ fun c _ ↦ (continuous_weight ε c).smul continuous_const
  exact (hden.continuousOn.inv₀ fun x hx ↦ (sum_weight_pos hx).ne').smul hnum.continuousOn

/-- The weighted average at `x` is a convex combination of the values `y c` at the centers `c`
within `ε` of `x`. -/
theorem blend_mem_convexHull {t : Finset X} {ε : ℝ} {x : X} (hx : ∃ c ∈ t, dist x c < ε)
    (y : X → E) : blend t ε y x ∈ convexHull ℝ (y '' {c | c ∈ t ∧ dist x c < ε}) := by
  classical
  rw [blend, ← Finset.centerMass_filter_ne_zero]
  refine Finset.centerMass_mem_convexHull _ (fun c _ ↦ weight_nonneg ε c x) ?_ fun c hc ↦ ?_
  · rw [Finset.sum_filter_ne_zero]
    exact sum_weight_pos hx
  · obtain ⟨hct, hc0⟩ := Finset.mem_filter.1 hc
    exact ⟨c, ⟨hct, weight_pos_iff.1 ((weight_nonneg ε c x).lt_of_ne' hc0)⟩, rfl⟩

/-- Schauder's projection maps the union of the balls of radius `ε` about the points of `t` into
the convex hull of `t`. -/
theorem blend_id_mem_convexHull {t : Finset E} {ε : ℝ} {x : E} (hx : ∃ c ∈ t, dist x c < ε) :
    blend t ε id x ∈ convexHull ℝ (t : Set E) :=
  convexHull_mono (by rintro _ ⟨c, ⟨hc, -⟩, rfl⟩; exact hc) (blend_mem_convexHull hx id)

/-- Schauder's projection moves each point of the union of the balls of radius `ε` about the
points of `t` by less than `ε`. -/
theorem dist_blend_id_lt {t : Finset E} {ε : ℝ} {x : E} (hx : ∃ c ∈ t, dist x c < ε) :
    dist (blend t ε id x) x < ε := by
  have hsub : id '' {c | c ∈ t ∧ dist x c < ε} ⊆ ball x ε := by
    rintro _ ⟨c, ⟨-, hxc⟩, rfl⟩
    rw [mem_ball, dist_comm]
    exact hxc
  exact convexHull_min hsub (convex_ball x ε) (blend_mem_convexHull hx id)

end SchauderProjection
