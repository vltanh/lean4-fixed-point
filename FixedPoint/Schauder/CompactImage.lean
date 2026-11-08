module

public import FixedPoint.Schauder.Compact
public import Mathlib.Analysis.Convex.TotallyBounded

/-!
# Schauder's fixed-point theorem for maps with relatively compact image

* `Schauder.isCompact_closedConvexHull` (Mazur's theorem, S. Mazur, *Über die kleinste konvexe
  Menge, die eine gegebene kompakte Menge enthält*, Studia Math. 2 (1930), 7–9; Schauder's
  Hilfssatz II): in a real Banach space, the closed convex hull of a totally bounded set, for
  instance of a relatively compact set, is compact.
* `Schauder.exists_fixedPoint_of_isCompact_closure_image` (**Schauder's fixed-point theorem**,
  Satz II of Schauder's paper): in a real Banach space, a continuous self-map `f` of a nonempty
  closed convex set `s` whose image `f '' s` is relatively compact has a fixed point in `s`.
  Schauder's "kompakt" is Fréchet's, that is, relatively compact.

## Proof

The closed convex hull `K` of `f '' s` is compact (Mazur), lies in `s`, which is closed and convex
and contains `f '' s`, and `f` maps it into `f '' s ⊆ K`. Schauder's theorem for compact convex sets
(`Schauder.exists_fixedPoint`) gives a fixed point in `K ⊆ s`. This is Schauder's proof.

Completeness of the space is used only by Mazur's theorem.
-/

@[expose] public section

open Set

namespace Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Mazur's theorem**: in a real Banach space, the closed convex hull of a totally bounded set,
for instance of a relatively compact set, is compact. -/
theorem isCompact_closedConvexHull {t : Set E} (ht : TotallyBounded t) :
    IsCompact (closedConvexHull ℝ t) := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact ht.convexHull.closure.isCompact_of_isClosed isClosed_closure

/-- **Schauder's fixed-point theorem**, second form: in a real Banach space, a map that is
continuous on a nonempty closed convex set `s`, maps `s` into itself and has a relatively compact
image `f '' s` has a fixed point in `s`. -/
theorem exists_fixedPoint_of_isCompact_closure_image {s : Set E} (hconv : Convex ℝ s)
    (hcl : IsClosed s) (hne : s.Nonempty) {f : E → E} (hmaps : MapsTo f s s)
    (hf : ContinuousOn f s) (himg : IsCompact (closure (f '' s))) : ∃ x ∈ s, f x = x := by
  have hKs : closedConvexHull ℝ (f '' s) ⊆ s :=
    closedConvexHull_min (image_subset_iff.2 hmaps) hconv hcl
  have hfK : MapsTo f (closedConvexHull ℝ (f '' s)) (closedConvexHull ℝ (f '' s)) :=
    fun x hx ↦ subset_closedConvexHull (mem_image_of_mem f (hKs hx))
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, hfy⟩ := exists_fixedPoint convex_closedConvexHull
    (isCompact_closedConvexHull (himg.totallyBounded.subset subset_closure))
    ⟨f x, subset_closedConvexHull (mem_image_of_mem f hx)⟩ hfK (hf.mono hKs)
  exact ⟨y, hKs hy, hfy⟩

end Schauder
