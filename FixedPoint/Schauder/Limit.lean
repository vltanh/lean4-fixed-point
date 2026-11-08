/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The limit in Schauder's proof

`Schauder.exists_fixedPoint_of_forall_dist_lt`: if a map `f`, continuous on a compact set `s`,
moves some point of `s` by less than `ε` for every `ε > 0`, then it has a fixed point in `s`. This
is the last step of Schauder's proof of his Satz I (J. Schauder, *Der Fixpunktsatz in
Funktionalräumen*, Studia Math. 2 (1930), 171–180): "Da ein solcher Punkt `d` für jedes `ε`
gefunden werden kann, so schließen wir … wegen der Kompaktheit und Abgeschlossenheit der Menge `H`
auf das Vorhandensein eines Fixpunktes." Points `x n` moved by less than `1 / (n + 1)` have a
subsequence converging to some `a ∈ s`, and `f a = a` by continuity.
-/

@[expose] public section

open Set Filter Topology

namespace Schauder

variable {X : Type*} [MetricSpace X]

/-- If `f` is continuous on a compact set `s` and moves some point of `s` by less than `ε` for
every `ε > 0`, then `f` has a fixed point in `s`. -/
theorem exists_fixedPoint_of_forall_dist_lt {s : Set X} (hcomp : IsCompact s) {f : X → X}
    (hf : ContinuousOn f s) (happrox : ∀ ε > 0, ∃ x ∈ s, dist (f x) x < ε) :
    ∃ x ∈ s, f x = x := by
  choose x hxs hx using fun n : ℕ ↦ happrox _ (Nat.one_div_pos_of_nat (α := ℝ) (n := n))
  obtain ⟨a, has, φ, hφ, hlim⟩ := hcomp.tendsto_subseq hxs
  have hfa : Tendsto (fun k ↦ f (x (φ k))) atTop (𝓝 (f a)) :=
    (hf a has).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k ↦ hxs _⟩)
  have hdist : Tendsto (fun k ↦ dist (f (x (φ k))) (x (φ k))) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hx (φ k)).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  exact ⟨a, has, dist_le_zero.1 (le_of_eq (tendsto_nhds_unique (hfa.dist hlim) hdist))⟩

end Schauder
