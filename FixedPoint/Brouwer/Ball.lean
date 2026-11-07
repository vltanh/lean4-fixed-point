module

public import FixedPoint.Brouwer.SmoothFixedPoint
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Brouwer's fixed-point theorem for closed balls, and the no-retraction theorem

Let `E` be a finite-dimensional real inner product space, for instance
`EuclideanSpace ℝ (Fin n)`.

* `Brouwer.exists_fixedPoint_closedBall`: a map that is continuous on a closed ball and maps it
  into itself has a fixed point in it.
* `Brouwer.no_retraction`: no map, continuous on the closed unit ball, maps it into the unit
  sphere and fixes the unit sphere.

## Proof

For the unit ball, suppose that `f` has no fixed point, so that `‖f x - x‖ ≥ ε > 0` on the
closed ball `B̄`. Extend `f` to `E` through the radial retraction of `E` onto `B̄`, and smooth it by
convolution with a bump function (`Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`).
Dividing the smoothed map by `1 + η` keeps it in `B̄`, and gives a smooth map `q` of `B̄` into
itself with `‖q - f‖ < ε` on `B̄` (`Brouwer.exists_contDiff_approx`). A fixed point of `q`
(`Brouwer.exists_fixedPoint_of_contDiffAt`) would satisfy `‖f x - x‖ < ε`. Other balls follow by
an affine change of variables. A retraction `r` onto the sphere would make `-r` a self-map of the
ball without fixed point.
-/

@[expose] public section

open Set Metric
open scoped ContDiff

namespace Brouwer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The radial retraction of `E` onto its closed unit ball. -/
noncomputable def radialRetraction (x : E) : E := (max 1 ‖x‖)⁻¹ • x

theorem continuous_radialRetraction : Continuous (radialRetraction : E → E) :=
  ((continuous_const.max continuous_norm).inv₀ fun x ↦
    (one_pos.trans_le (le_max_left 1 ‖x‖)).ne').smul continuous_id

theorem radialRetraction_mem (x : E) : radialRetraction x ∈ closedBall (0 : E) 1 := by
  have hpos : 0 < max 1 ‖x‖ := one_pos.trans_le (le_max_left _ _)
  rw [mem_closedBall_zero_iff, radialRetraction, norm_smul, norm_inv,
    Real.norm_of_nonneg hpos.le, inv_mul_le_iff₀ hpos, mul_one]
  exact le_max_right _ _

theorem radialRetraction_of_mem {x : E} (hx : x ∈ closedBall (0 : E) 1) :
    radialRetraction x = x := by
  rw [radialRetraction, max_eq_left (mem_closedBall_zero_iff.mp hx), inv_one, one_smul]

variable [FiniteDimensional ℝ E]

/-- A continuous self-map of the closed unit ball is uniformly approximated on it by smooth maps
of the closed unit ball into itself. -/
theorem exists_contDiff_approx {f : E → E} (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1))
    (hf : ContinuousOn f (closedBall 0 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : E → E, ContDiff ℝ ∞ q ∧ MapsTo q (closedBall 0 1) (closedBall 0 1) ∧
      ∀ x ∈ closedBall (0 : E) 1, ‖q x - f x‖ < ε := by
  set F : E → E := fun x ↦ f (radialRetraction x) with hF_def
  have hF : Continuous F :=
    hf.comp_continuous continuous_radialRetraction radialRetraction_mem
  have hFK : ∀ x ∈ closedBall (0 : E) 1, F x = f x := fun x hx ↦ by
    simp only [hF_def, radialRetraction_of_mem hx]
  set η : ℝ := ε / 4 with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : E) 2).uniformContinuousOn_of_continuous hF.continuousOn) η hη
  obtain ⟨c, hc, hcF⟩ :=
    hF.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min hδ one_pos)
  have hcK : ∀ a ∈ closedBall (0 : E) 1, ‖c a - f a‖ ≤ η := by
    intro a ha
    have ha2 : a ∈ closedBall (0 : E) 2 := closedBall_subset_closedBall (by norm_num) ha
    have := hcF a η fun x hx ↦ by
      have hxa : dist x a < min δ 1 := hx
      have hx2 : x ∈ closedBall (0 : E) 2 := by
        rw [mem_closedBall_zero_iff] at ha ⊢
        have h1 := norm_sub_norm_le x a
        rw [← dist_eq_norm] at h1
        linarith [min_le_right δ 1]
      exact (hδF x hx2 a ha2 (hxa.trans_le (min_le_left _ _))).le
    rwa [dist_eq_norm, hFK a ha] at this
  refine ⟨(1 + η)⁻¹ • c, hc.const_smul _, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have h1 : ‖c x‖ ≤ 1 + η := by
      have := norm_le_insert' (c x) (f x)
      linarith [hcK x hx, mem_closedBall_zero_iff.mp (hmaps hx)]
    rw [mem_closedBall_zero_iff, Pi.smul_apply, norm_smul, norm_inv,
      Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by positivity), mul_one]
    exact h1
  · have h1 : ‖c x‖ ≤ 1 + η := by
      have := norm_le_insert' (c x) (f x)
      linarith [hcK x hx, mem_closedBall_zero_iff.mp (hmaps hx)]
    have h2 : ‖(1 + η)⁻¹ • c x - c x‖ ≤ η := by
      rw [show (1 + η)⁻¹ • c x - c x = ((1 + η)⁻¹ - 1) • c x by rw [sub_smul, one_smul],
        norm_smul, Real.norm_eq_abs,
        abs_of_nonpos (by rw [sub_nonpos]; exact inv_le_one_of_one_le₀ (by linarith))]
      calc -((1 + η)⁻¹ - 1) * ‖c x‖ ≤ -((1 + η)⁻¹ - 1) * (1 + η) := by
            gcongr
            rw [neg_nonneg, sub_nonpos]
            exact inv_le_one_of_one_le₀ (by linarith)
        _ = η := by field_simp; ring
    calc ‖((1 + η)⁻¹ • c) x - f x‖ = ‖((1 + η)⁻¹ • c x - c x) + (c x - f x)‖ := by
          rw [Pi.smul_apply, sub_add_sub_cancel]
      _ ≤ ‖(1 + η)⁻¹ • c x - c x‖ + ‖c x - f x‖ := norm_add_le _ _
      _ ≤ η + η := add_le_add h2 (hcK x hx)
      _ < ε := by rw [hη_def]; linarith

/-- Brouwer's fixed-point theorem for the closed unit ball. -/
theorem exists_fixedPoint_closedBall_zero_one {f : E → E}
    (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) (hf : ContinuousOn f (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : E) 1, f x = x := by
  by_contra! hne
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    (nonempty_closedBall.mpr zero_le_one) (hf.sub continuousOn_id).norm
  have hε : 0 < ‖f x₀ - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne x₀ hx₀))
  obtain ⟨q, hq, hqmaps, hqf⟩ := exists_contDiff_approx hmaps hf hε
  obtain ⟨x, hx, hqx⟩ := exists_fixedPoint_of_contDiffAt
    (fun x _ ↦ (contDiff_infty.mp hq 1).contDiffAt) hqmaps
  have h1 : ‖f x₀ - x₀‖ ≤ ‖f x - x‖ := isMinOn_iff.mp hmin x hx
  have h2 := hqf x hx
  rw [hqx, norm_sub_rev] at h2
  exact absurd h1 (not_le.mpr h2)

/-- **Brouwer's fixed-point theorem** for a closed ball of a finite-dimensional real inner product
space: a map that is continuous on the ball and maps it into itself has a fixed point in it. -/
theorem exists_fixedPoint_closedBall {c : E} {R : ℝ} (hR : 0 ≤ R) {f : E → E}
    (hmaps : MapsTo f (closedBall c R) (closedBall c R)) (hf : ContinuousOn f (closedBall c R)) :
    ∃ x ∈ closedBall c R, f x = x := by
  rcases hR.eq_or_lt with rfl | hR
  · refine ⟨c, mem_closedBall_self le_rfl, ?_⟩
    simpa using hmaps (mem_closedBall_self le_rfl)
  have hφ : MapsTo (fun y : E ↦ c + R • y) (closedBall 0 1) (closedBall c R) := fun y hy ↦ by
    rw [mem_closedBall_zero_iff] at hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hR.le]
    nlinarith
  have hφc : Continuous fun y : E ↦ c + R • y := continuous_const.add (continuous_const_smul R)
  have hg : MapsTo (fun y ↦ R⁻¹ • (f (c + R • y) - c)) (closedBall 0 1) (closedBall 0 1) :=
    fun y hy ↦ by
      have h := hmaps (hφ hy)
      rw [mem_closedBall, dist_eq_norm] at h
      rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hR.le,
        inv_mul_le_iff₀ hR, mul_one]
      exact h
  obtain ⟨y, hy, hfy⟩ := exists_fixedPoint_closedBall_zero_one hg
    (((hf.comp hφc.continuousOn hφ).sub continuousOn_const).const_smul R⁻¹)
  refine ⟨c + R • y, hφ hy, ?_⟩
  have := congrArg (R • ·) hfy
  simp only [smul_inv_smul₀ hR.ne'] at this
  exact sub_eq_iff_eq_add'.mp this

/-- **The no-retraction theorem**: there is no retraction of the closed unit ball of a
finite-dimensional real inner product space onto its unit sphere, that is, no map that is
continuous on the closed ball, maps it into the sphere and fixes every point of the sphere. -/
theorem no_retraction :
    ¬ ∃ r : E → E, ContinuousOn r (closedBall 0 1) ∧ MapsTo r (closedBall 0 1) (sphere 0 1) ∧
      ∀ x ∈ sphere (0 : E) 1, r x = x := by
  rintro ⟨r, hr, hmaps, hfix⟩
  obtain ⟨x, hx, hrx⟩ := exists_fixedPoint_closedBall_zero_one (f := fun x ↦ -r x)
    (fun x hx ↦ by
      rw [mem_closedBall_zero_iff, norm_neg]
      exact (mem_sphere_zero_iff_norm.mp (hmaps hx)).le) hr.neg
  have hxn : ‖x‖ = 1 := by
    rw [← hrx, norm_neg]
    exact mem_sphere_zero_iff_norm.mp (hmaps hx)
  have hrx' : -x = x := by
    have := hrx
    rwa [hfix x (mem_sphere_zero_iff_norm.mpr hxn)] at this
  have h0 : x = 0 := by
    have h3 : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hrx']
      exact neg_add_cancel x
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  rw [h0, norm_zero] at hxn
  exact zero_ne_one hxn

end Brouwer
