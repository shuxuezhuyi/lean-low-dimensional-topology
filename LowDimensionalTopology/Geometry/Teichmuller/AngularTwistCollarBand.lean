module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistInfinitesimal
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PointLineFormulas
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Closed angular bands inside canonical strips

The tangent of the inclination to the imaginary axis is the real-to-imaginary
coordinate ratio. A strict bound on this tangent places the entire closed
angular support of an elementary coefficient inside the canonical open strip.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The closed angular band supporting the elementary angular coefficient. -/
def closedAngularBand (θ : Width) : Set ℍ :=
  {z | Complex.arg (z : ℂ) ∈ interval θ}

/-- Angular-band membership is a bound on deviation from the imaginary axis. -/
theorem mem_closedAngularBand_iff (θ : Width) (z : ℍ) :
    z ∈ closedAngularBand θ ↔ |Complex.arg (z : ℂ) - Real.pi / 2| ≤ (θ : ℝ) := by
  change (Real.pi / 2 - (θ : ℝ) ≤ Complex.arg (z : ℂ) ∧
    Complex.arg (z : ℂ) ≤ Real.pi / 2 + (θ : ℝ)) ↔ _
  rw [abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- A strict slope bound includes the closed angular band in the canonical
open strip of the actual logarithmic dilation. -/
theorem closedAngularBand_subset_hCanonicalRegion (θ : Width) {t : ℝ}
    (ht : 0 < t) (hθ : Real.tan (θ : ℝ) * Real.sinh t < 1) :
    closedAngularBand θ ⊆ Hyperbolic.hCanonicalRegion (Fuchsian.hLogDilationSL t) := by
  intro z hz
  have hi : Hyperbolic.verticalInclination 0 z ≤ (θ : ℝ) := by
    rw [Hyperbolic.verticalInclination_zero_eq_arg]
    exact (mem_closedAngularBand_iff θ z).mp hz
  have himem := Hyperbolic.verticalInclination_mem_Ico 0 z
  have htan : Real.tan (Hyperbolic.verticalInclination 0 z) ≤ Real.tan (θ : ℝ) :=
    Real.strictMonoOn_tan.monotoneOn
      ⟨by linarith [Real.pi_pos, himem.1], himem.2⟩
      ⟨by linarith [Real.pi_pos, θ.property.1], θ.property.2⟩ hi
  have hr : |z.re| / z.im ≤ Real.tan (θ : ℝ) := by
    rw [← Hyperbolic.verticalLine_pointDist_sinh_inclination] at htan
    simpa only [Hyperbolic.verticalLine_pointDist_sinh, sub_zero] using htan
  have hcoord : |z.re| ≤ Real.tan (θ : ℝ) * z.im :=
    (div_le_iff₀ z.im_pos).mp hr
  have hs : 0 < Real.sinh t := Real.sinh_pos_iff.mpr ht
  rw [Fuchsian.hCanonicalRegion_logDilation]
  change |Real.sinh t * z.re| < z.im
  rw [abs_mul, abs_of_pos hs]
  calc
    Real.sinh t * |z.re| ≤ Real.sinh t * (Real.tan (θ : ℝ) * z.im) :=
      mul_le_mul_of_nonneg_left hcoord hs.le
    _ = (Real.tan (θ : ℝ) * Real.sinh t) * z.im := by ring
    _ < 1 * z.im := mul_lt_mul_of_pos_right hθ z.im_pos
    _ = z.im := one_mul _

/-- An explicit positive angular width with a strict canonical-strip margin. -/
def canonicalBandWidth (t : ℝ) (ht : 0 < t) : Width :=
  ⟨Real.arctan (1 / (2 * Real.sinh t)),
    Real.arctan_pos.mpr (one_div_pos.mpr
      (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr ht))),
    Real.arctan_lt_pi_div_two _⟩

/-- The explicit width uses exactly half the permitted canonical-strip slope. -/
theorem tan_canonicalBandWidth_mul_sinh (t : ℝ) (ht : 0 < t) :
    Real.tan (canonicalBandWidth t ht : ℝ) * Real.sinh t = 1 / 2 := by
  change Real.tan (Real.arctan (1 / (2 * Real.sinh t))) * Real.sinh t = 1 / 2
  rw [Real.tan_arctan, ← div_div]
  exact div_mul_cancel₀ (1 / 2) (Real.sinh_pos_iff.mpr ht).ne'

/-- The chosen closed angular support lies strictly inside the actual canonical strip. -/
theorem closedAngularBand_canonicalBandWidth_subset_hCanonicalRegion (t : ℝ) (ht : 0 < t) :
    closedAngularBand (canonicalBandWidth t ht) ⊆
      Hyperbolic.hCanonicalRegion (Fuchsian.hLogDilationSL t) := by
  apply closedAngularBand_subset_hCanonicalRegion _ ht
  rw [tan_canonicalBandWidth_mul_sinh]
  norm_num

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
