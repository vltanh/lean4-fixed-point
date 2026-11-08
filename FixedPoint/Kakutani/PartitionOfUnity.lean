/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Brouwer.Convex
public import FixedPoint.Kakutani.Limit
public import FixedPoint.Schauder.Projection
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Kakutani's theorem through a partition of unity

A second proof of Kakutani's fixed-point theorem for compact convex sets of finite-dimensional
real normed spaces, `Kakutani.PartitionOfUnity.exists_fixedPoint`, with the same statement as
`Kakutani.exists_fixedPoint`. Kakutani's proof (`FixedPoint/Kakutani/Simplex.lean`) approximates
`φ` by piecewise-linear maps on barycentric subdivisions of a simplex; this one approximates it by
averages over a partition of unity, which need no simplex.

1. **Approximation** (`Kakutani.PartitionOfUnity.exists_approx`). For `δ > 0`, cover `s` by
   finitely many open balls of radius `δ` centered at points `c ∈ s`, pick `y c ∈ φ c`, and let
   `F x` be the average of the `y c` weighted by the partition of unity of Schauder's projection
   (`Schauder.blend`). Then `F` maps `s` continuously into `s`, so it has a fixed point `x` by
   Brouwer's theorem. By Carathéodory's theorem, `x` is a convex combination of `dim V + 1` points
   `y j ∈ φ (a j)` with `a j ∈ s` within `δ` of `x`.
2. **Limit** (`Kakutani.exists_mem_self_of_approx`), as in Kakutani's proof, with
   `δ = 1 / (n + 1)`.
-/

@[expose] public section

open Set Filter Topology Module

namespace Kakutani.PartitionOfUnity

/-- **Carathéodory's theorem** with exactly `finrank + 1` points: a point of the convex hull of `T`
in a finite-dimensional real vector space is a convex combination of `finrank + 1` points of `T`,
repetitions and zero weights allowed. -/
theorem exists_sum_fin_eq_of_mem_convexHull {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {T : Set V} {x : V} (hx : x ∈ convexHull ℝ T) :
    ∃ (w : Fin (finrank ℝ V + 1) → ℝ) (z : Fin (finrank ℝ V + 1) → V),
      (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, z j ∈ T) ∧ ∑ j, w j • z j = x := by
  classical
  obtain ⟨ι, _, z, w, hzT, hind, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ Fintype.card (Fin (finrank ℝ V + 1)) := by
    rw [Fintype.card_fin]
    exact (AffineIndependent.card_le_finrank_succ hind).trans
      (Nat.succ_le_succ (Submodule.finrank_le _))
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  have hext : ∀ j, j ∉ range e → Function.extend e w 0 j = 0 := fun j hj ↦
    Function.extend_apply' _ _ _ (by simpa using hj)
  refine ⟨Function.extend e w 0, Function.extend e z fun _ ↦ z i₀, fun j ↦ ?_, ?_,
    fun j ↦ ?_, ?_⟩
  · by_cases h : j ∈ range e
    · obtain ⟨i, rfl⟩ := h
      rw [e.injective.extend_apply]
      exact (hw0 i).le
    · rw [hext j h]
  · rw [← hw1]
    exact (Fintype.sum_of_injective e e.injective _ _ hext
      fun i ↦ (e.injective.extend_apply _ _ _).symm).symm
  · by_cases h : j ∈ range e
    · obtain ⟨i, rfl⟩ := h
      rw [e.injective.extend_apply]
      exact hzT ⟨i, rfl⟩
    · rw [Function.extend_apply' _ _ _ (by simpa using h)]
      exact hzT ⟨i₀, rfl⟩
  · rw [← hwz]
    refine (Fintype.sum_of_injective e e.injective _ _ (fun j hj ↦ ?_)
      fun i ↦ ?_).symm
    · rw [hext j hj, zero_smul]
    · rw [e.injective.extend_apply, e.injective.extend_apply]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The approximation: for every `δ > 0`, some `x ∈ s` is a convex combination
`∑ w j • y j` of `finrank + 1` points `y j ∈ φ (a j)`, with `a j ∈ s` within `δ` of `x`. -/
theorem exists_approx {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)
    {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s) (hφne : ∀ x ∈ s, (φ x).Nonempty) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ x ∈ s, ∃ (w : Fin (finrank ℝ V + 1) → ℝ) (a y : Fin (finrank ℝ V + 1) → V),
      (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧
        (∀ j, a j ∈ s ∧ y j ∈ φ (a j) ∧ dist (a j) x < δ) ∧ ∑ j, w j • y j = x := by
  classical
  obtain ⟨t, hts, htfin, hcover⟩ := hcomp.finite_cover_balls hδ
  have hcov : ∀ x ∈ s, ∃ c ∈ htfin.toFinset, dist x c < δ := fun x hx ↦ by
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcover hx)
    exact ⟨c, htfin.mem_toFinset.2 hc, hxc⟩
  choose! g hg using hφne
  -- the approximating map: the values `g c ∈ φ c` averaged with Schauder's partition of unity
  let F := Schauder.blend htfin.toFinset δ g
  have hT : ∀ x, g '' {c | c ∈ htfin.toFinset ∧ dist x c < δ} ⊆ s := fun x ↦ by
    rintro _ ⟨c, ⟨hc, -⟩, rfl⟩
    have hcs : c ∈ s := hts (htfin.mem_toFinset.1 hc)
    exact hmaps c hcs (hg c hcs)
  have hF : MapsTo F s s := fun x hx ↦
    convexHull_min (hT x) hconv (Schauder.blend_mem_convexHull (hcov x hx) g)
  obtain ⟨x, hx, hFx⟩ := Brouwer.exists_fixedPoint hconv hcomp hne hF
    ((Schauder.continuousOn_blend _ δ g).mono hcov)
  have hxT : x ∈ convexHull ℝ (g '' {c | c ∈ htfin.toFinset ∧ dist x c < δ}) := by
    have h := Schauder.blend_mem_convexHull (hcov x hx) g
    rwa [show Schauder.blend htfin.toFinset δ g x = x from hFx] at h
  obtain ⟨w, z, hw0, hw1, hz, hsum⟩ := exists_sum_fin_eq_of_mem_convexHull hxT
  choose a ha using hz
  refine ⟨x, hx, w, a, z, hw0, hw1, fun j ↦ ?_, hsum⟩
  obtain ⟨⟨hc, hdist⟩, hgz⟩ := ha j
  have has : a j ∈ s := hts (htfin.mem_toFinset.1 hc)
  exact ⟨has, hgz ▸ hg _ has, by rw [dist_comm]; exact hdist⟩

/-- **Kakutani's fixed-point theorem**, proved through a partition of unity: in a
finite-dimensional real normed space, if `φ` sends each point of a nonempty compact convex set `s`
to a nonempty convex subset of `s` and its graph `{(x, y) | x ∈ s, y ∈ φ x}` is closed, then
`x ∈ φ x` for some `x ∈ s`. -/
theorem exists_fixedPoint {s : Set V} (hconv : Convex ℝ s) (hcomp : IsCompact s)
    (hne : s.Nonempty) {φ : V → Set V} (hmaps : ∀ x ∈ s, φ x ⊆ s)
    (hφne : ∀ x ∈ s, (φ x).Nonempty) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) : ∃ x ∈ s, x ∈ φ x := by
  choose x hx w a y hw0 hw1 hay hsum using fun n : ℕ ↦
    exists_approx hconv hcomp hne hmaps hφne (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  exact exists_mem_self_of_approx hcomp hmaps hφconv hgraph tendsto_one_div_add_atTop_nhds_zero_nat
    hx hw0 hw1 (fun n j ↦ ⟨(hay n j).1, (hay n j).2.1, (hay n j).2.2.le⟩) hsum

end Kakutani.PartitionOfUnity
