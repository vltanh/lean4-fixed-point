module

public import FixedPoint.Brouwer.Ball
public import FixedPoint.Brouwer.NearestPoint
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# Brouwer's fixed-point theorem for compact convex sets

* `Brouwer.exists_fixedPoint`: in a finite-dimensional real normed space, a map that is
  continuous on a nonempty compact convex set `s` and maps `s` into itself has a fixed point
  in `s`.
* `Brouwer.exists_fixedPoint_continuousMap`: the same for a continuous map `C(s, s)`.

## Proof

Through a linear isomorphism with `EuclideanSpace ℝ (Fin n)` we may assume that the space has an
inner product. There, `s` lies in a closed ball `B̄`, and is a retract of the whole space through
the nearest-point map `π` (`Brouwer.exists_lipschitzWith_retraction`). The map `f ∘ π` sends `B̄`
continuously into `s ⊆ B̄`, so has a fixed point `x` (`Brouwer.exists_fixedPoint_closedBall`);
then `x = f (π x) ∈ s`, so `π x = x` and `f x = x`.
-/

@[expose] public section

open Set Metric

namespace Brouwer

/-- Brouwer's fixed-point theorem for compact convex sets of a finite-dimensional real inner
product space. -/
theorem exists_fixedPoint_of_innerProductSpace {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {s : Set F} (hconv : Convex ℝ s)
    (hcomp : IsCompact s) (hne : s.Nonempty) {f : F → F} (hmaps : MapsTo f s s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, f x = x := by
  obtain ⟨π, hπ, hπs, hπfix⟩ := exists_lipschitzWith_retraction hne hcomp.isClosed hconv
  obtain ⟨R, hR, hsR⟩ := hcomp.isBounded.subset_closedBall_lt 0 0
  obtain ⟨x, -, hfx⟩ := exists_fixedPoint_closedBall (c := 0) hR.le (f := fun x ↦ f (π x))
    (fun x _ ↦ hsR (hmaps (hπs x))) (hf.comp_continuous hπ.continuous hπs).continuousOn
  have hxs : x ∈ s := hfx ▸ hmaps (hπs x)
  exact ⟨x, hxs, by simpa [hπfix x hxs] using hfx⟩

/-- **Brouwer's fixed-point theorem**: in a finite-dimensional real normed space, a map that is
continuous on a nonempty compact convex set `s` and maps `s` into itself has a fixed point in
`s`. -/
theorem exists_fixedPoint {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {f : V → V} (hmaps : MapsTo f s s) (hf : ContinuousOn f s) :
    ∃ x ∈ s, f x = x := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hmaps' : MapsTo (fun y ↦ e (f (e.symm y))) (e '' s) (e '' s) := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, hmaps hx, by simp⟩
  have hf' : ContinuousOn (fun y ↦ e (f (e.symm y))) (e '' s) :=
    e.continuous.comp_continuousOn (hf.comp e.symm.continuous.continuousOn
      (by rintro y ⟨x, hx, rfl⟩; simpa using hx))
  obtain ⟨y, ⟨x, hx, rfl⟩, hfy⟩ := exists_fixedPoint_of_innerProductSpace
    (hconv.linear_image (e : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))))
    (hcomp.image e.continuous) (hne.image e) hmaps' hf'
  exact ⟨x, hx, e.injective (by simpa using hfy)⟩

/-- **Brouwer's fixed-point theorem** for a continuous self-map of a nonempty compact convex set
of a finite-dimensional real normed space. -/
theorem exists_fixedPoint_continuousMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) (f : C(s, s)) : ∃ x, f x = x := by
  classical
  let F : V → V := fun v ↦ if h : v ∈ s then (f ⟨v, h⟩ : V) else v
  have hmaps : MapsTo F s s := fun v hv ↦ by simp [F, hv]
  have hF : ContinuousOn F s := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : s.domRestrict F = fun x : s ↦ (f x : V) := funext fun x ↦ by
      simp [Set.domRestrict_apply, F, x.2]
    rw [this]
    exact continuous_subtype_val.comp f.continuous
  obtain ⟨x, hx, hfx⟩ := exists_fixedPoint hconv hcomp hne hmaps hF
  exact ⟨⟨x, hx⟩, Subtype.ext (by simpa [F, hx] using hfx)⟩

end Brouwer
