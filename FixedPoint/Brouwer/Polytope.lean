/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Brouwer.Convex

/-!
# Brouwer's theorem for polytopes in a normed space

`Brouwer.exists_fixedPoint_convexHull_of_finite`: in a real normed space of any dimension, a map
that is continuous on the convex hull `K` of a nonempty finite set `t` and maps `K` into itself
has a fixed point in `K`. The span `W` of `t` is finite-dimensional and contains `K`, so Brouwer's
theorem (`Brouwer.exists_fixedPoint`) applies to `K` as a compact convex subset of `W`.
-/

@[expose] public section

open Set

namespace Brouwer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Brouwer's fixed-point theorem** for the convex hull of a nonempty finite set in a real
normed space of any dimension. -/
theorem exists_fixedPoint_convexHull_of_finite {t : Set E} (ht : t.Finite) (hne : t.Nonempty)
    {f : E → E} (hmaps : MapsTo f (convexHull ℝ t) (convexHull ℝ t))
    (hf : ContinuousOn f (convexHull ℝ t)) :
    ∃ x ∈ convexHull ℝ t, f x = x := by
  classical
  let W := Submodule.span ℝ t
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ ht
  have hKW : convexHull ℝ t ⊆ W := convexHull_min Submodule.subset_span W.convex
  let s : Set W := (↑) ⁻¹' convexHull ℝ t
  have himg : ((↑) : W → E) '' s = convexHull ℝ t :=
    image_preimage_eq_of_subset (by rwa [Subtype.range_coe])
  have hconv : Convex ℝ s := (convex_convexHull ℝ t).linear_preimage W.subtype
  have hcomp : IsCompact s := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
    exact ht.isCompact_convexHull ℝ
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, Submodule.subset_span hx⟩, subset_convexHull ℝ t hx⟩
  let g : W → W := fun w ↦ if h : f w ∈ W then ⟨f w, h⟩ else w
  have hg : ∀ w ∈ s, (g w : E) = f w := fun w hw ↦ by
    have h : f w ∈ W := hKW (hmaps hw)
    simp [g, h]
  have hgmaps : MapsTo g s s := fun w hw ↦ by
    change (g w : E) ∈ convexHull ℝ t
    rw [hg w hw]
    exact hmaps hw
  have hgcont : ContinuousOn g s := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (hf.comp continuous_subtype_val.continuousOn fun w hw ↦ hw).congr fun w hw ↦ hg w hw
  obtain ⟨w, hw, hgw⟩ := exists_fixedPoint hconv hcomp hsne hgmaps hgcont
  exact ⟨w, hw, by rw [← hg w hw, hgw]⟩

end Brouwer
