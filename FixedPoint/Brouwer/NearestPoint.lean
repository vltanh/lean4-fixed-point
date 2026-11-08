/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# The nearest-point retraction onto a closed convex set

In a real inner product space `F` that is complete, every nonempty closed convex set `s` is the
image of a `1`-Lipschitz retraction of `F`: send each point to its nearest point in `s`
(`Brouwer.exists_lipschitzWith_retraction`). The nearest point `π u` exists by
`exists_norm_eq_iInf_of_complete_convex`, and is characterized by `⟪u - π u, w - π u⟫ ≤ 0` for
`w ∈ s` (`norm_eq_iInf_iff_real_inner_le_zero`); adding these inequalities for `u = x` and `u = y`
gives `‖π x - π y‖² ≤ ⟪x - y, π x - π y⟫ ≤ ‖x - y‖ ‖π x - π y‖`.
-/

@[expose] public section

open Set
open scoped RealInnerProductSpace

namespace Brouwer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A nonempty closed convex subset of a complete real inner product space is a `1`-Lipschitz
retract of the whole space, through the nearest-point map. -/
theorem exists_lipschitzWith_retraction {s : Set F} (hne : s.Nonempty) (hcl : IsClosed s)
    (hconv : Convex ℝ s) :
    ∃ π : F → F, LipschitzWith 1 π ∧ (∀ x, π x ∈ s) ∧ ∀ x ∈ s, π x = x := by
  have h : ∀ u : F, ∃ v ∈ s, ∀ w ∈ s, ⟪u - v, w - v⟫ ≤ 0 := fun u ↦ by
    obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv u
    exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin⟩
  choose π hπs hπ using h
  refine ⟨π, LipschitzWith.of_dist_le_mul fun x y ↦ ?_, hπs, fun x hx ↦ ?_⟩
  · have h1 := hπ x (π y) (hπs y)
    have h2 := hπ y (π x) (hπs x)
    have key : ⟪x - y, π x - π y⟫ =
        ‖π x - π y‖ ^ 2 - ⟪x - π x, π y - π x⟫ - ⟪y - π y, π x - π y⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    have h3 : ‖π x - π y‖ ^ 2 ≤ ‖x - y‖ * ‖π x - π y‖ :=
      (by linarith : ‖π x - π y‖ ^ 2 ≤ ⟪x - y, π x - π y⟫).trans (real_inner_le_norm _ _)
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    rcases (norm_nonneg (π x - π y)).eq_or_lt with h0 | h0
    · rw [← h0]
      exact norm_nonneg _
    · nlinarith
  · have h1 := hπ x x hx
    rw [real_inner_self_eq_norm_sq] at h1
    have h2 : ‖x - π x‖ = 0 := by nlinarith [norm_nonneg (x - π x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp h2)).symm

end Brouwer
