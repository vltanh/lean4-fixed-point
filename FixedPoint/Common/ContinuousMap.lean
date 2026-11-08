/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.ContinuousOn

/-!
# Fixed points of continuous self-maps of a subset

`FixedPoint.exists_fixedPoint_continuousMap_of`: if every map `f : X → X` that is continuous on
`s` and maps `s` into itself has a fixed point in `s`, then so does every `f : C(s, s)`. The map
`f` extends to `X` by the identity outside `s`. This gives the `C(s, s)` forms of Brouwer's and
Schauder's theorems.
-/

@[expose] public section

open Set

namespace FixedPoint

/-- A fixed-point theorem for the maps that are continuous on `s` and map `s` into itself gives
the same theorem for the continuous maps `C(s, s)`. -/
theorem exists_fixedPoint_continuousMap_of {X : Type*} [TopologicalSpace X] {s : Set X}
    (h : ∀ f : X → X, MapsTo f s s → ContinuousOn f s → ∃ x ∈ s, f x = x) (f : C(s, s)) :
    ∃ x, f x = x := by
  classical
  let F : X → X := fun v ↦ if hv : v ∈ s then (f ⟨v, hv⟩ : X) else v
  have hmaps : MapsTo F s s := fun v hv ↦ by simp [F, hv]
  have hF : ContinuousOn F s := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : s.domRestrict F = fun x : s ↦ (f x : X) := funext fun x ↦ by
      simp [Set.domRestrict_apply, F, x.2]
    rw [this]
    exact continuous_subtype_val.comp f.continuous
  obtain ⟨x, hx, hfx⟩ := h F hmaps hF
  exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [F, hx] using hfx)⟩

end FixedPoint
