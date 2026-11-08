/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The limit in Kakutani's proof

`Kakutani.exists_mem_self_of_approx`: let `s` be compact and `φ` send each point of `s` to a
convex subset of `s`, with closed graph over `s`. Suppose that for each `n`, the point `x n ∈ s`
is a convex combination `∑ j, w n j • y n j` of `m` points `y n j ∈ φ (a n j)`, where the points
`a n j ∈ s` are within `δ n` of `x n`, and `δ n → 0`. Then `x ∈ φ x` for some `x ∈ s`.

This is the second half of Kakutani's proof of his Theorem 1 (Duke Math. J. 8 (1941), 457–459):
take a subsequence along which `x n → x₀`, `w n → w₀` and `y n → y₀`. Then `a n j → x₀`, so
`y₀ j ∈ φ x₀` as the graph is closed, and `x₀ = ∑ j, w₀ j • y₀ j ∈ φ x₀` as `φ x₀` is convex.
Kakutani takes the subsequences one after the other; here one subsequence of the triples
`(x n, w n, y n)` serves for all.
-/

@[expose] public section

open Set Filter Topology

namespace Kakutani

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The limit in Kakutani's proof: approximate fixed points `x n = ∑ j, w n j • y n j`, with
`y n j ∈ φ (a n j)` and `a n j` within `δ n → 0` of `x n`, give a point `x ∈ φ x`. -/
theorem exists_mem_self_of_approx {s : Set V} (hcomp : IsCompact s) {φ : V → Set V}
    (hmaps : ∀ x ∈ s, φ x ⊆ s) (hφconv : ∀ x ∈ s, Convex ℝ (φ x))
    (hgraph : IsClosed {p : V × V | p.1 ∈ s ∧ p.2 ∈ φ p.1}) {m : ℕ} {x : ℕ → V}
    {w : ℕ → Fin m → ℝ} {a y : ℕ → Fin m → V} {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hx : ∀ n, x n ∈ s) (hw0 : ∀ n j, 0 ≤ w n j) (hw1 : ∀ n, ∑ j, w n j = 1)
    (hay : ∀ n j, a n j ∈ s ∧ y n j ∈ φ (a n j) ∧ dist (a n j) (x n) ≤ δ n)
    (hsum : ∀ n, ∑ j, w n j • y n j = x n) : ∃ x ∈ s, x ∈ φ x := by
  have hK : IsCompact (s ×ˢ ((univ.pi fun _ : Fin m ↦ Icc (0 : ℝ) 1) ×ˢ
      univ.pi fun _ : Fin m ↦ s)) :=
    hcomp.prod ((isCompact_univ_pi fun _ ↦ isCompact_Icc).prod (isCompact_univ_pi fun _ ↦ hcomp))
  have hw1' : ∀ n j, w n j ≤ 1 := fun n j ↦ (hw1 n) ▸
    Finset.single_le_sum (fun i _ ↦ hw0 n i) (Finset.mem_univ j)
  obtain ⟨⟨x₀, w₀, y₀⟩, ⟨hx₀, -, -⟩, ψ, hψ, hlim⟩ :=
    hK.tendsto_subseq (x := fun n ↦ (x n, w n, y n))
      fun n ↦ ⟨hx n, fun j _ ↦ ⟨hw0 n j, hw1' n j⟩, fun j _ ↦ hmaps _ (hay n j).1 (hay n j).2.1⟩
  have hxlim : Tendsto (fun k ↦ x (ψ k)) atTop (𝓝 x₀) :=
    (continuous_fst.tendsto _).comp hlim
  have hwlim : ∀ j, Tendsto (fun k ↦ w (ψ k) j) atTop (𝓝 (w₀ j)) := fun j ↦
    (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).tendsto _).comp hlim
  have hylim : ∀ j, Tendsto (fun k ↦ y (ψ k) j) atTop (𝓝 (y₀ j)) := fun j ↦
    (((continuous_apply j).comp (continuous_snd.comp continuous_snd)).tendsto _).comp hlim
  -- the points `a n j` converge to `x₀` too
  have halim : ∀ j, Tendsto (fun k ↦ a (ψ k) j) atTop (𝓝 x₀) := fun j ↦
    hxlim.congr_dist (squeeze_zero (fun _ ↦ dist_nonneg)
      (fun k ↦ by rw [dist_comm]; exact (hay (ψ k) j).2.2) (hδ.comp hψ.tendsto_atTop))
  -- the limits `y₀ j` lie in `φ x₀`, as the graph is closed
  have hy₀ : ∀ j, y₀ j ∈ φ x₀ := fun j ↦
    (hgraph.mem_of_tendsto ((halim j).prodMk_nhds (hylim j))
      (Eventually.of_forall fun k ↦ ⟨(hay (ψ k) j).1, (hay (ψ k) j).2.1⟩)).2
  have hw₀0 : ∀ j, 0 ≤ w₀ j := fun j ↦ ge_of_tendsto' (hwlim j) fun k ↦ hw0 (ψ k) j
  have hw₀1 : ∑ j, w₀ j = 1 :=
    tendsto_nhds_unique (tendsto_finsetSum _ fun j _ ↦ hwlim j)
      (by simpa only [hw1] using tendsto_const_nhds)
  have heq : ∑ j, w₀ j • y₀ j = x₀ :=
    tendsto_nhds_unique (tendsto_finsetSum _ fun j _ ↦ (hwlim j).smul (hylim j))
      (by simpa only [hsum] using hxlim)
  -- `φ x₀` is convex
  exact ⟨x₀, hx₀, heq ▸ (hφconv x₀ hx₀).sum_mem (fun j _ ↦ hw₀0 j) hw₀1 fun j _ ↦ hy₀ j⟩

end Kakutani
