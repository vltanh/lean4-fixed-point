/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# From Euclidean space to finite-dimensional normed spaces

A finite-dimensional real normed space `V` is linearly homeomorphic to
`EuclideanSpace ℝ (Fin (finrank ℝ V))`, and the isomorphism carries compact convex sets, maps
continuous on them, convex sets and closed graphs to the same. So a fixed-point theorem for compact
convex sets of Euclidean space holds in `V`:

* `FixedPoint.exists_fixedPoint_of_euclidean`, for maps (Brouwer's theorem);
* `FixedPoint.exists_mem_self_of_euclidean`, for set-valued maps (Kakutani's theorem).
-/

@[expose] public section

open Set Module

namespace FixedPoint

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A fixed-point theorem for continuous self-maps of compact convex sets of Euclidean space holds
in every finite-dimensional real normed space. -/
theorem exists_fixedPoint_of_euclidean
    (H : ∀ s : Set (EuclideanSpace ℝ (Fin (finrank ℝ V))), Convex ℝ s → IsCompact s →
      s.Nonempty → ∀ f, MapsTo f s s → ContinuousOn f s → ∃ x ∈ s, f x = x)
    {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty) {f : V → V}
    (hmaps : MapsTo f s s) (hf : ContinuousOn f s) : ∃ x ∈ s, f x = x := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hmaps' : MapsTo (fun y ↦ e (f (e.symm y))) (e '' s) (e '' s) := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, hmaps hx, by simp⟩
  have hf' : ContinuousOn (fun y ↦ e (f (e.symm y))) (e '' s) :=
    e.continuous.comp_continuousOn (hf.comp e.symm.continuous.continuousOn
      (by rintro y ⟨x, hx, rfl⟩; simpa using hx))
  obtain ⟨y, ⟨x, hx, rfl⟩, hfy⟩ := H _
    (hconv.linear_image (e : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V))))
    (hcomp.image e.continuous) (hne.image e) _ hmaps' hf'
  exact ⟨x, hx, e.injective (by simpa using hfy)⟩

/-- A fixed-point theorem for set-valued maps of compact convex sets of Euclidean space, with
closed graph and nonempty convex values, holds in every finite-dimensional real normed space. -/
theorem exists_mem_self_of_euclidean
    (H : ∀ s : Set (EuclideanSpace ℝ (Fin (finrank ℝ V))), Convex ℝ s → IsCompact s →
      s.Nonempty → ∀ φ : _ → Set _, (∀ x ∈ s, φ x ⊆ s) → (∀ x ∈ s, (φ x).Nonempty) →
        (∀ x ∈ s, Convex ℝ (φ x)) →
          IsClosed {p : EuclideanSpace ℝ (Fin (finrank ℝ V)) ×
            EuclideanSpace ℝ (Fin (finrank ℝ V)) | p.1 ∈ s ∧ p.2 ∈ φ p.1} → ∃ x ∈ s, x ∈ φ x)
    {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty) {φ : V → Set V}
    (hmaps : ∀ x ∈ s, φ x ⊆ s) (hφne : ∀ x ∈ s, (φ x).Nonempty)
    (hφconv : ∀ x ∈ s, Convex ℝ (φ x)) (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) :
    ∃ x ∈ s, x ∈ φ x := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hs' : e.symm ⁻¹' s = e '' s := (e.image_eq_preimage_symm s).symm
  obtain ⟨y, hy, hyφ⟩ := H (e.symm ⁻¹' s)
    (hconv.linear_preimage e.symm.toLinearEquiv.toLinearMap)
    (hs' ▸ hcomp.image e.continuous) (hs' ▸ hne.image e) (fun y ↦ e.symm ⁻¹' φ (e.symm y))
    (fun y hy z hz ↦ hmaps _ hy hz)
    (fun y hy ↦ by
      obtain ⟨z, hz⟩ := hφne _ hy
      exact ⟨e z, by simpa using hz⟩)
    (fun y hy ↦ (hφconv _ hy).linear_preimage e.symm.toLinearEquiv.toLinearMap)
    (hgraph.preimage (e.symm.continuous.prodMap e.symm.continuous))
  exact ⟨e.symm y, hy, hyφ⟩

end FixedPoint
