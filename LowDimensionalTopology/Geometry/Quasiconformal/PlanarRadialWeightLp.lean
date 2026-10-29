module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Radial inverse powers in the original planar Lp spaces

The singularity is controlled by the genuine real dimension two. The exact
real-power conventions also cover the point zero. Holder multiplication then
gives absolute integrability for the actual real or complex input function.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Metric MeasureTheory
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- A radial power lies in the prescribed planar Lq when its q-th power has
exponent below the real dimension two. No positive-radius premise is needed. -/
theorem norm_rpow_memLp_ball {q a : ℝ} (hq : 0 < q) (haq : a * q < 2) (R : ℝ) :
    MemLp (fun z : ℂ => ‖z‖ ^ (-a)) (ENNReal.ofReal q)
      (volume.restrict (ball (0 : ℂ) R)) := by
  have hm : AEStronglyMeasurable (fun z : ℂ => ‖z‖ ^ (-a)) volume :=
    (continuous_norm.measurable.pow_const (-a)).aestronglyMeasurable
  have hint : IntegrableOn (fun z : ℂ => ‖z‖ ^ (-(a * q)))
      (ball 0 R) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := a * q)
      (by rw [Complex.finrank_real_complex]; decide) ?_
      (Filter.Eventually.of_forall fun z => ?_)
      (continuous_norm.measurable.pow_const (-(a * q))).aestronglyMeasurable
    · simpa [Complex.finrank_real_complex] using haq
    · rw [one_mul]
      exact le_of_eq (Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _))
  apply (integrable_norm_rpow_iff hm.restrict
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top).mp
  have heq : (fun z : ℂ => ‖(‖z‖ ^ (-a) : ℝ)‖ ^ (ENNReal.ofReal q).toReal) =
      (fun z : ℂ => ‖z‖ ^ (-(a * q))) := by
    funext z
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _),
      ENNReal.toReal_ofReal hq.le, ← Real.rpow_mul (norm_nonneg z), neg_mul]
  rw [heq]
  exact hint

/-- The actual Holder product with this weight is absolutely integrable.
The statement applies to real-valued and complex-valued functions alike. -/
theorem integrable_norm_rpow_smul_ball {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q a R : ℝ} (hpq : p.HolderConjugate q) (haq : a * q < 2)
    {h : ℂ → E} (hh : MemLp h (ENNReal.ofReal p)
      (volume.restrict (ball (0 : ℂ) R))) :
    IntegrableOn (fun z : ℂ => ‖z‖ ^ (-a) • h z) (ball 0 R) volume := by
  let : ENNReal.HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal p) 1 :=
    hpq.symm.ennrealOfReal
  have hw := norm_rpow_memLp_ball hpq.symm.pos haq R
  exact memLp_one_iff_integrable.mp (hw.smul hh)

/-- Literal complex multiplication by the same actual radial weight. -/
theorem integrable_mul_norm_rpow_ball {p q a R : ℝ}
    (hpq : p.HolderConjugate q) (haq : a * q < 2)
    {h : ℂ → ℂ} (hh : MemLp h (ENNReal.ofReal p)
      (volume.restrict (ball (0 : ℂ) R))) :
    IntegrableOn (fun z : ℂ => h z * ((‖z‖ ^ (-a) : ℝ) : ℂ)) (ball 0 R) volume := by
  simpa only [Complex.real_smul, mul_comm] using
    integrable_norm_rpow_smul_ball hpq haq hh

end LowDimensionalTopology.Geometry.Quasiconformal
