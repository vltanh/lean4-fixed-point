/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import FixedPoint.Brouwer.SmoothRetraction
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A `C¹` self-map of the closed unit ball has a fixed point

Let `E` be a finite-dimensional real inner product space. If `q : E → E` is continuously
differentiable at every point of the closed unit ball `B̄` and maps `B̄` into itself, then `q` has a
fixed point in `B̄` (`Brouwer.exists_fixedPoint_of_contDiffAt`).

Otherwise, sending `x ∈ B̄` to the point where the ray from `q x` through `x` meets the unit sphere
(`Brouwer.rayRetraction`) is a `C¹` retraction of `B̄` onto the sphere, which
`Brouwer.no_contDiffAt_retraction` rules out. That point is `x + λ • u` with `u = x - q x` and
`λ = (√D - ⟪x, u⟫) / ‖u‖²`, `D = ⟪x, u⟫² - ‖u‖² (‖x‖² - 1)`, the larger root of
`‖x + λ • u‖² = 1`. The discriminant `D` is positive on `B̄` (`Brouwer.disc_pos`), so the
retraction is `C¹` there; on the sphere `λ = 0`.
-/

@[expose] public section

open Set Metric
open scoped RealInnerProductSpace

namespace Brouwer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The discriminant `⟪x, u⟫² - ‖u‖² (‖x‖² - 1)` of the equation `‖x + λ • u‖² = 1` in `λ`. -/
noncomputable def disc (x u : E) : ℝ := ⟪x, u⟫ ^ 2 - ‖u‖ ^ 2 * (‖x‖ ^ 2 - 1)

/-- The larger root `λ` of `‖x + λ • u‖² = 1`. -/
noncomputable def rayParam (x u : E) : ℝ := (√(disc x u) - ⟪x, u⟫) / ‖u‖ ^ 2

/-- The point where the ray from `q x` through `x` meets the unit sphere. -/
noncomputable def rayRetraction (q : E → E) (x : E) : E :=
  x + rayParam x (x - q x) • (x - q x)

theorem norm_add_rayParam_smul {x u : E} (hu : u ≠ 0) (hD : 0 ≤ disc x u) :
    ‖x + rayParam x u • u‖ = 1 := by
  have ha : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
  have hs : √(disc x u) ^ 2 = ⟪x, u⟫ ^ 2 - ‖u‖ ^ 2 * (‖x‖ ^ 2 - 1) := Real.sq_sqrt hD
  have hl : rayParam x u * ‖u‖ ^ 2 = √(disc x u) - ⟪x, u⟫ := by
    rw [rayParam]
    field_simp
  have hsq : ‖x + rayParam x u • u‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h : ‖u‖ ^ 2 * (‖x‖ ^ 2 + 2 * (rayParam x u * ⟪x, u⟫) + rayParam x u ^ 2 * ‖u‖ ^ 2 - 1)
        = 0 := by
      linear_combination (⟪x, u⟫ + rayParam x u * ‖u‖ ^ 2 + √(disc x u)) * hl + hs
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h ha.ne'
    · linarith
  have h0 := norm_nonneg (x + rayParam x u • u)
  nlinarith

theorem rayParam_eq_zero {x u : E} (hx : ‖x‖ = 1) (hb : 0 ≤ ⟪x, u⟫) : rayParam x u = 0 := by
  have : disc x u = ⟪x, u⟫ ^ 2 := by simp [disc, hx]
  rw [rayParam, this, Real.sqrt_sq hb, sub_self, zero_div]

/-- If `‖x‖ = 1`, `‖y‖ ≤ 1` and `y ≠ x`, then `⟪x, x - y⟫ > 0`. -/
theorem inner_sub_pos {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1) (hxy : y ≠ x) :
    0 < ⟪x, x - y⟫ := by
  have h1 : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm)) 2
  rw [norm_sub_sq_real, hx] at h1
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hx]
  nlinarith [norm_nonneg y]

/-- The discriminant is positive on the closed unit ball, away from fixed points. -/
theorem disc_pos {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : y ≠ x) : 0 < disc x (x - y) := by
  rcases hx.lt_or_eq with hlt | heq
  · have h1 : 0 < ‖x - y‖ ^ 2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm)) 2
    have h2 : ‖x‖ ^ 2 - 1 < 0 := by nlinarith [norm_nonneg x]
    unfold disc
    nlinarith [sq_nonneg ⟪x, x - y⟫]
  · have := inner_sub_pos heq hy hxy
    simp only [disc, heq]
    simpa using pow_pos this 2

theorem contDiffAt_rayRetraction {q : E → E} {x : E} (hq : ContDiffAt ℝ 1 q x)
    (hx : ‖x‖ ≤ 1) (hqx : ‖q x‖ ≤ 1) (hne : q x ≠ x) : ContDiffAt ℝ 1 (rayRetraction q) x := by
  have hu : ContDiffAt ℝ 1 (fun y ↦ y - q y) x := contDiffAt_fun_id.sub hq
  have hb : ContDiffAt ℝ 1 (fun y ↦ ⟪y, y - q y⟫) x := contDiffAt_fun_id.inner ℝ hu
  have ha : ContDiffAt ℝ 1 (fun y ↦ ‖y - q y‖ ^ 2) x := hu.norm_sq ℝ
  have hD : ContDiffAt ℝ 1 (fun y ↦ disc y (y - q y)) x :=
    (hb.pow 2).sub (ha.mul ((contDiffAt_fun_id.norm_sq ℝ).sub contDiffAt_const))
  have hsq : ContDiffAt ℝ 1 (fun y ↦ √(disc y (y - q y))) x :=
    hD.sqrt (disc_pos hx hqx hne).ne'
  have hl : ContDiffAt ℝ 1 (fun y ↦ rayParam y (y - q y)) x :=
    (hsq.sub hb).div ha (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)) 2).ne'
  exact contDiffAt_fun_id.add (hl.smul hu)

/-- **Brouwer's fixed-point theorem for `C¹` maps**: a map that is `C¹` at every point of the
closed unit ball and maps it into itself has a fixed point there. -/
theorem exists_fixedPoint_of_contDiffAt [FiniteDimensional ℝ E] {q : E → E}
    (hq : ∀ x ∈ closedBall (0 : E) 1, ContDiffAt ℝ 1 q x)
    (hmaps : MapsTo q (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : E) 1, q x = x := by
  by_contra! hne
  have hqn : ∀ x ∈ closedBall (0 : E) 1, ‖q x‖ ≤ 1 := fun x hx ↦
    mem_closedBall_zero_iff.mp (hmaps hx)
  refine no_contDiffAt_retraction (r := rayRetraction q) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    (fun x hx ↦ ?_)
  · exact contDiffAt_rayRetraction (hq x hx) (mem_closedBall_zero_iff.mp hx) (hqn x hx)
      (hne x hx)
  · rw [mem_sphere_zero_iff_norm]
    exact norm_add_rayParam_smul (sub_ne_zero.mpr (hne x hx).symm)
      (disc_pos (mem_closedBall_zero_iff.mp hx) (hqn x hx) (hne x hx)).le
  · have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hxK : x ∈ closedBall (0 : E) 1 := sphere_subset_closedBall hx
    rw [rayRetraction, rayParam_eq_zero hxn (inner_sub_pos hxn (hqn x hxK) (hne x hxK)).le,
      zero_smul, add_zero]

end Brouwer
