module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Determinants of `1 + t • A` are polynomials in `t`

For a continuous linear endomorphism `A` of a finite-dimensional real normed space `E` of
dimension `d`, the determinant `det (1 + t • A)` is a polynomial of degree at most `d` in `t`.
We record two consequences used by the analytic proof of Brouwer's fixed-point theorem:

* `Brouwer.exists_polynomial_integral_det`: if `A` depends on a parameter `x` and each
  `x ↦ det (1 + t • A x)` is integrable, then `t ↦ ∫ det (1 + t • A x) dx` is a polynomial
  function of `t`. Instead of integrating the coefficients of the polynomials (whose measurability
  in `x` would need an argument of its own), we write `det (1 + t • A x)` through its values at
  the nodes `t = 0, 1, …, d` by Lagrange interpolation (`Brouwer.det_id_add_smul_eq_sum`).
* `Brouwer.det_id_add_pos`: `det (1 + A) > 0` when `‖A‖ < 1`.
-/

@[expose] public section

open Polynomial MeasureTheory

namespace Brouwer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The polynomial `det (1 + X • A)`, whose value at `t` is `det (1 + t • A)`, written in the
matrix of `A` in the basis `Module.finBasis ℝ E`. -/
noncomputable def detPoly (A : E →L[ℝ] E) : ℝ[X] :=
  Matrix.det ((X : ℝ[X]) •
      (LinearMap.toMatrix (Module.finBasis ℝ E) (Module.finBasis ℝ E) (A : E →ₗ[ℝ] E)).map C +
    (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ).map C)

theorem eval_detPoly (A : E →L[ℝ] E) (t : ℝ) :
    (detPoly A).eval t = (ContinuousLinearMap.id ℝ E + t • A).det := by
  rw [detPoly, ← coe_evalRingHom, RingHom.map_det, ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (Module.finBasis ℝ E)]
  congr 1
  simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_id, map_add, map_smul, LinearMap.toMatrix_id]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    RingHom.mapMatrix_apply, coe_evalRingHom, eval_mul, eval_X, eval_C,
    LinearMap.toMatrix_apply]
  ring

theorem natDegree_detPoly_le (A : E →L[ℝ] E) : (detPoly A).natDegree ≤ Module.finrank ℝ E := by
  exact (natDegree_det_X_add_C_le (α := ℝ) _ _).trans (by simp)

/-- The nodes `0, 1, …, d` of the Lagrange interpolation, where `d = finrank ℝ E`. -/
noncomputable abbrev nodes (E : Type*) [AddCommGroup E] [Module ℝ E] : Finset ℕ :=
  Finset.range (Module.finrank ℝ E + 1)

/-- `det (1 + t • A)` through its values at `t = 0, 1, …, d` (Lagrange interpolation). -/
theorem det_id_add_smul_eq_sum (A : E →L[ℝ] E) (t : ℝ) :
    (ContinuousLinearMap.id ℝ E + t • A).det =
      ∑ i ∈ nodes E, (ContinuousLinearMap.id ℝ E + (i : ℝ) • A).det *
        (Lagrange.basis (nodes E) (fun i : ℕ ↦ (i : ℝ)) i).eval t := by
  have hinj : Set.InjOn (fun i : ℕ ↦ (i : ℝ)) (nodes E) := fun i _ j _ h ↦ Nat.cast_injective h
  have hdeg : (detPoly A).degree < (nodes E).card := by
    rw [Finset.card_range]
    exact (degree_le_of_natDegree_le (natDegree_detPoly_le A)).trans_lt
      (by exact_mod_cast Nat.lt_succ_self (Module.finrank ℝ E))
  conv_lhs => rw [← eval_detPoly, Lagrange.eq_interpolate hinj hdeg]
  simp [Lagrange.interpolate_apply, eval_finsetSum, eval_detPoly]

/-- If `x ↦ det (1 + t • A x)` is integrable for every `t`, then its integral is a polynomial
function of `t`. -/
theorem exists_polynomial_integral_det {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : α → E →L[ℝ] E)
    (hA : ∀ t : ℝ, Integrable (fun x ↦ (ContinuousLinearMap.id ℝ E + t • A x).det) μ) :
    ∃ p : ℝ[X], ∀ t : ℝ, ∫ x, (ContinuousLinearMap.id ℝ E + t • A x).det ∂μ = p.eval t := by
  refine ⟨∑ i ∈ nodes E, C (∫ x, (ContinuousLinearMap.id ℝ E + (i : ℝ) • A x).det ∂μ) *
    Lagrange.basis (nodes E) (fun i : ℕ ↦ (i : ℝ)) i, fun t ↦ ?_⟩
  calc ∫ x, (ContinuousLinearMap.id ℝ E + t • A x).det ∂μ
      = ∫ x, ∑ i ∈ nodes E, (ContinuousLinearMap.id ℝ E + (i : ℝ) • A x).det *
          (Lagrange.basis (nodes E) (fun i : ℕ ↦ (i : ℝ)) i).eval t ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x ↦ det_id_add_smul_eq_sum (A x) t)
    _ = _ := by
        rw [integral_finsetSum (nodes E) fun i _ ↦ (hA (i : ℝ)).mul_const _]
        simp [eval_finsetSum, integral_mul_const]

/-- `1 + A` is invertible, so has a nonzero determinant, when `‖A‖ < 1`. -/
theorem det_id_add_ne_zero {A : E →L[ℝ] E} (hA : ‖A‖ < 1) :
    (ContinuousLinearMap.id ℝ E + A).det ≠ 0 := by
  intro h
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot] at h
  apply h
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hv' : v = -A v := eq_neg_of_add_eq_zero_left (by simpa using hv)
  have hle : ‖v‖ ≤ ‖A‖ * ‖v‖ :=
    calc ‖v‖ = ‖A v‖ := by rw [← norm_neg (A v), ← hv']
      _ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
  have : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
  exact norm_le_zero_iff.mp this

/-- `det (1 + A) > 0` when `‖A‖ < 1`: the determinant does not vanish along the segment from
`1` to `1 + A`. -/
theorem det_id_add_pos {A : E →L[ℝ] E} (hA : ‖A‖ < 1) :
    0 < (ContinuousLinearMap.id ℝ E + A).det := by
  have hcont : Continuous fun s : ℝ ↦ (ContinuousLinearMap.id ℝ E + s • A).det :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  by_contra hle
  push Not at hle
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by simpa using hle, by simp [ContinuousLinearMap.det]⟩)
  refine det_id_add_ne_zero (A := s • A) ?_ hs0
  calc ‖s • A‖ = |s| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 * ‖A‖ := by
        gcongr
        rw [abs_le]
        constructor <;> linarith [hs.1, hs.2]
    _ < 1 := by simpa using hA

end Brouwer
