module

public import FixedPoint.Brouwer.DetPolynomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# There is no `C¹` retraction of the closed unit ball onto its sphere

Let `E` be a finite-dimensional real inner product space, `B` its open unit ball and `S` its unit
sphere. This file proves `Brouwer.no_contDiffAt_retraction`: there is no map `r : E → E`,
continuously differentiable at every point of the closed ball `B̄`, that maps `B̄` into `S` and
fixes every point of `S`.

## Proof

This is the analytic proof of Milnor (1978), in the form given by Rogers (1980). Let `g = r - id`,
whose derivative is bounded by `L` on `B̄`, so that `g` is `L`-Lipschitz on `B̄`, and let
`f t = id + t • g = (1 - t) • id + t • r`.

* For `0 < t < 1 / (L + 1)`, `f t` is injective on `B`, maps `B` into `B` (as `‖r‖ = 1`), and
  `f t '' B` is open, since `f t` is a Lipschitz perturbation of the identity
  (`ApproximatesLinearOn.open_image`). As `f t` fixes `S`, `f t '' B` is also closed in `B`, so
  `f t '' B = B` by connectedness (`Brouwer.image_ball_eq_ball`). The change of variables formula
  gives `∫_B |det D(f t)| = vol B`, and `det D(f t) = det (1 + t • Dg) > 0` since
  `‖t • Dg‖ < 1`.
* `t ↦ ∫_B det (1 + t • Dg)` is a polynomial (`Brouwer.exists_polynomial_integral_det`), equal to
  `vol B` on an interval, hence everywhere.
* At `t = 1` the integrand is `det Dr`, which vanishes on `B`: differentiating `‖r‖² = 1` shows
  that the range of `Dr x` is orthogonal to `r x ≠ 0` (`Brouwer.det_fderiv_eq_zero`). So
  `vol B = 0`, a contradiction.

## References

* J. Milnor, *Analytic proofs of the "hairy ball theorem" and the Brouwer fixed point theorem*,
  Amer. Math. Monthly 85 (1978), 521–524.
* C. A. Rogers, *A less strange version of Milnor's proof of Brouwer's fixed-point theorem*,
  Amer. Math. Monthly 87 (1980), 525–527.
-/

@[expose] public section

open Set Metric MeasureTheory Polynomial Filter
open scoped NNReal Topology

namespace Brouwer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- If `‖r‖ = 1` near `x`, then the derivative of `r` at `x` is singular: its range is orthogonal
to `r x`. -/
theorem det_fderiv_eq_zero {r : E → E} {x : E} (hr : DifferentiableAt ℝ r x)
    (h : ∀ᶠ y in 𝓝 x, ‖r y‖ = 1) : (fderiv ℝ r x).det = 0 := by
  have h1 : HasFDerivAt (fun y ↦ ‖r y‖ ^ 2) (2 • (innerSL ℝ (r x)).comp (fderiv ℝ r x)) x :=
    hr.hasFDerivAt.norm_sq
  have h2 : HasFDerivAt (fun y ↦ ‖r y‖ ^ 2) (0 : E →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq (h.mono fun y hy ↦ by simp [hy])
  have h3 := h1.unique h2
  have hrx : ‖r x‖ = 1 := h.self_of_nhds
  by_contra hdet
  have hker : LinearMap.ker (fderiv ℝ r x : E →ₗ[ℝ] E) = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  obtain ⟨v, hv⟩ :=
    (LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp hker)) (r x)
  have h4 := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) h3
  simp only [FunLike.coe_smul, ContinuousLinearMap.coe_comp, Pi.smul_apply,
    Function.comp_apply, innerSL_apply_apply, zero_apply] at h4
  rw [show (fderiv ℝ r x) v = r x from hv, real_inner_self_eq_norm_sq, hrx] at h4
  norm_num at h4

/-- A map that is `C¹` at every point of the closed unit ball has a bounded derivative there, and
is Lipschitz on it. -/
theorem exists_bound_fderiv {g : E → E} (hg : ∀ x ∈ closedBall (0 : E) 1, ContDiffAt ℝ 1 g x) :
    ∃ L : ℝ≥0, (∀ x ∈ closedBall (0 : E) 1, ‖fderiv ℝ g x‖ ≤ L) ∧
      LipschitzOnWith L g (closedBall 0 1) := by
  have hcont : ContinuousOn (fderiv ℝ g) (closedBall 0 1) := fun x hx ↦
    ((hg x hx).continuousAt_fderiv one_ne_zero).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hcont
  refine ⟨C.toNNReal, fun x hx ↦ (hC x hx).trans (Real.le_coe_toNNReal C), ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (f' := fderiv ℝ g)
    (fun x hx ↦ ((hg x hx).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt)
    (fun x hx ↦ ?_) (convex_closedBall (0 : E) 1)
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC x hx).trans (Real.le_coe_toNNReal C)

/-- A map, continuous on the closed unit ball, that maps the open ball into itself, fixes the unit
sphere and maps the open ball onto an open set, maps the open ball onto itself. -/
theorem image_ball_eq_ball {φ : E → E} (hcont : ContinuousOn φ (closedBall 0 1))
    (hmaps : MapsTo φ (ball 0 1) (ball 0 1)) (hfix : ∀ x ∈ sphere (0 : E) 1, φ x = x)
    (hopen : IsOpen (φ '' ball 0 1)) : φ '' ball 0 1 = ball 0 1 := by
  refine Subset.antisymm hmaps.image_subset ?_
  refine (convex_ball (0 : E) 1).isPreconnected.subset_of_closure_inter_subset hopen ?_ ?_
  · exact ⟨φ 0, hmaps (mem_ball_self one_pos), mem_image_of_mem _ (mem_ball_self one_pos)⟩
  · rintro y ⟨hy, hyB⟩
    have hK : IsClosed (φ '' closedBall 0 1) :=
      ((isCompact_closedBall (0 : E) 1).image_of_continuousOn hcont).isClosed
    obtain ⟨x, hx, rfl⟩ := closure_minimal (image_mono ball_subset_closedBall) hK hy
    by_cases hx1 : x ∈ ball (0 : E) 1
    · exact mem_image_of_mem _ hx1
    · have hxS : x ∈ sphere (0 : E) 1 := by
        simp only [mem_closedBall, mem_ball, mem_sphere, not_lt] at hx hx1 ⊢
        exact le_antisymm hx hx1
      rw [hfix x hxS] at hyB
      exact absurd hyB hx1

/-- **No `C¹` retraction**: no map `r`, continuously differentiable at every point of the closed
unit ball, maps the closed unit ball into the unit sphere and fixes the unit sphere. -/
theorem no_contDiffAt_retraction {r : E → E}
    (hr : ∀ x ∈ closedBall (0 : E) 1, ContDiffAt ℝ 1 r x)
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1)) (hfix : ∀ x ∈ sphere (0 : E) 1, r x = x) :
    False := by
  borelize E
  set μ : Measure E := Measure.addHaar
  set g : E → E := fun x ↦ r x - x with hg_def
  have hg : ∀ x ∈ closedBall (0 : E) 1, ContDiffAt ℝ 1 g x := fun x hx ↦
    (hr x hx).sub contDiffAt_id
  obtain ⟨L, hLd, hLip⟩ := exists_bound_fderiv hg
  set A : E → E →L[ℝ] E := fun x ↦ fderiv ℝ g x with hA_def
  have hderiv : ∀ t : ℝ, ∀ x ∈ closedBall (0 : E) 1,
      HasFDerivAt (fun y ↦ y + t • g y) (ContinuousLinearMap.id ℝ E + t • A x) x :=
    fun t x hx ↦ (hasFDerivAt_id x).add
      (((hg x hx).differentiableAt one_ne_zero).hasFDerivAt.const_smul t)
  have hcontA : ContinuousOn A (closedBall 0 1) := fun x hx ↦
    ((hg x hx).continuousAt_fderiv one_ne_zero).continuousWithinAt
  set δ : ℝ := 1 / (L + 1) with hδ_def
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hδ : 0 < δ := by positivity
  have hδL : δ * L < 1 := by
    rw [hδ_def, one_div, inv_mul_lt_iff₀ (by positivity)]
    linarith
  have hδ1 : δ ≤ 1 := by
    rw [hδ_def, div_le_one (by positivity)]
    linarith
  -- For small `t > 0`, `∫_B det (1 + t • Dg) = vol B`.
  have hkey : ∀ t ∈ Ioo 0 δ, ∫ x in ball (0 : E) 1, (ContinuousLinearMap.id ℝ E + t • A x).det ∂μ
      = μ.real (ball 0 1) := by
    rintro t ⟨ht0, htδ⟩
    have htL : t * L < 1 := lt_of_le_of_lt (by gcongr) hδL
    have ht1 : t < 1 := htδ.trans_le hδ1
    have hlip : ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1, ‖g x - g y‖ ≤ L * ‖x - y‖ :=
      fun x hx y hy ↦ hLip.norm_sub_le (ball_subset_closedBall hx) (ball_subset_closedBall hy)
    have hinj : InjOn (fun y ↦ y + t • g y) (ball 0 1) := by
      intro x hx y hy hxy
      have h1 : x - y = t • (g y - g x) := by
        simp only at hxy
        rw [smul_sub]
        linear_combination (norm := module) hxy
      have h2 : ‖x - y‖ ≤ t * L * ‖x - y‖ :=
        calc ‖x - y‖ = t * ‖g y - g x‖ := by rw [h1, norm_smul, Real.norm_of_nonneg ht0.le]
          _ ≤ t * (L * ‖y - x‖) := by gcongr; exact hlip y hy x hx
          _ = t * L * ‖x - y‖ := by rw [norm_sub_rev]; ring
      have h3 : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
      exact sub_eq_zero.mp (norm_eq_zero.mp h3)
    have hopen : IsOpen ((fun y ↦ y + t • g y) '' ball 0 1) := by
      have happrox : ApproximatesLinearOn (fun y ↦ y + t • g y) (ContinuousLinearMap.id ℝ E)
          (ball 0 1) (t.toNNReal * L) := by
        intro x hx y hy
        have : x + t • g x - (y + t • g y) - ContinuousLinearMap.id ℝ E (x - y) =
            t • (g x - g y) := by
          simp only [ContinuousLinearMap.coe_id', id_eq, smul_sub]
          abel
        rw [this, norm_smul, Real.norm_of_nonneg ht0.le, NNReal.coe_mul,
          Real.coe_toNNReal _ ht0.le, mul_assoc]
        gcongr
        exact hlip x hx y hy
      refine happrox.open_image ⟨id, 1, fun y ↦ by simp, fun y ↦ rfl⟩ isOpen_ball (Or.inr ?_)
      rw [inv_one, ← NNReal.coe_lt_coe, NNReal.coe_mul, Real.coe_toNNReal _ ht0.le]
      exact_mod_cast htL
    have himage : (fun y ↦ y + t • g y) '' ball 0 1 = ball 0 1 := by
      refine image_ball_eq_ball (fun x hx ↦ (hderiv t x hx).continuousAt.continuousWithinAt)
        (fun x hx ↦ ?_) (fun x hx ↦ ?_) hopen
      · have hrx : ‖r x‖ = 1 := mem_sphere_zero_iff_norm.mp (hmaps (ball_subset_closedBall hx))
        have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
        rw [mem_ball_zero_iff]
        have : x + t • g x = (1 - t) • x + t • r x := by
          simp only [hg_def, smul_sub, sub_smul, one_smul]
          abel
        rw [this]
        calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
          _ = (1 - t) * ‖x‖ + t := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
                Real.norm_of_nonneg ht0.le, hrx, mul_one]
          _ < 1 := by nlinarith
      · simp [hg_def, hfix x hx]
    have hcv := integral_image_eq_integral_abs_det_fderiv_smul μ measurableSet_ball
      (fun x hx ↦ (hderiv t x (ball_subset_closedBall hx)).hasFDerivWithinAt) hinj
      (fun _ ↦ (1 : ℝ))
    rw [himage, setIntegral_const, smul_eq_mul, mul_one] at hcv
    rw [hcv]
    refine setIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
    simp only [smul_eq_mul, mul_one]
    refine (abs_of_pos (det_id_add_pos ?_)).symm
    calc ‖t • A x‖ = t * ‖A x‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
      _ ≤ t * L := by gcongr; exact hLd x (ball_subset_closedBall hx)
      _ < 1 := htL
  -- `t ↦ ∫_B det (1 + t • Dg)` is a polynomial, hence constant.
  have hint : ∀ t : ℝ, Integrable (fun x ↦ (ContinuousLinearMap.id ℝ E + t • A x).det)
      (μ.restrict (ball 0 1)) := by
    intro t
    have hc : ContinuousOn (fun x ↦ (ContinuousLinearMap.id ℝ E + t • A x).det)
        (closedBall 0 1) :=
      ContinuousLinearMap.continuous_det.comp_continuousOn
        (continuousOn_const.add (hcontA.const_smul t))
    exact (hc.integrableOn_compact (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  obtain ⟨p, hp⟩ := exists_polynomial_integral_det (μ.restrict (ball 0 1)) A hint
  have hpC : p = C (μ.real (ball (0 : E) 1)) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.Ioo_infinite hδ).mono fun t ht ↦ ?_
    simp only [mem_ofPred_eq, eval_C]
    rw [← hp t, hkey t ht]
  -- At `t = 1` the integrand is `det Dr = 0`.
  have hzero : ∫ x in ball (0 : E) 1, (ContinuousLinearMap.id ℝ E + (1 : ℝ) • A x).det ∂μ = 0 := by
    refine (setIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_).trans (integral_zero _ _)
    have hxK := ball_subset_closedBall hx
    have hrd : DifferentiableAt ℝ r x := (hr x hxK).differentiableAt one_ne_zero
    have hA1 : ContinuousLinearMap.id ℝ E + (1 : ℝ) • A x = fderiv ℝ r x := by
      rw [one_smul, hA_def]
      simp only [hg_def]
      rw [fderiv_fun_sub hrd differentiableAt_fun_id, fderiv_fun_id]
      abel
    simp only [hA1]
    refine det_fderiv_eq_zero hrd (Filter.eventually_of_mem (isOpen_ball.mem_nhds hx) ?_)
    exact fun y hy ↦ mem_sphere_zero_iff_norm.mp (hmaps (ball_subset_closedBall hy))
  have h1 := hp 1
  rw [hpC, eval_C, hzero] at h1
  have hpos : 0 < μ.real (ball (0 : E) 1) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  linarith

end Brouwer
