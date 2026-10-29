module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.StandardPantsSphereCaps

/-!
# The exact full closed ranges of the three standard spherical caps

All three boundary circles are retained in the removed cap ranges. The outer
cap additionally contains infinity, coming from zero in its closed-disc source.
-/

@[expose] public section
noncomputable section
open Set
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Mobius

/-- The actual closed cap carriers before the fixed sphere homeomorphism. -/
def pantsStandardExtendedCap (i : Fin 3) : Set ExtendedComplex :=
  if i = 0 then insert ∞ ((↑) '' {z : ℂ | 2 ≤ ‖z‖})
  else if i = 1 then (↑) '' {z : ℂ | ‖z + 1‖ ≤ (1 : ℝ) / 2}
  else (↑) '' {z : ℂ | ‖z - 1‖ ≤ (1 : ℝ) / 2}

private theorem outerCapChart_zero : pantsStandardCapChart 0 (0 : ℂ) = ∞ := by
  change affineHomeomorph 2 0 _ (reciprocal (0 : ℂ)) = ∞
  rw [reciprocal_zero, affineHomeomorph_infty]

private theorem outerCapChart_coe (z : ℂ) (hz : z ≠ 0) :
    pantsStandardCapChart 0 z = ((2 * z⁻¹ : ℂ) : ExtendedComplex) := by
  change affineHomeomorph 2 0 _ (reciprocal z) = _
  rw [reciprocal_coe z hz, affineHomeomorph_coe, add_zero]

private theorem outerCapChart_closedDisc_range :
    range (fun u : Complex.UnitClosedDisc => pantsStandardCapChart 0 ((u : ℂ) : ExtendedComplex)) =
      insert ∞ ((↑) '' {z : ℂ | 2 ≤ ‖z‖}) := by
  apply subset_antisymm
  · rintro _ ⟨u, rfl⟩
    by_cases hu : (u : ℂ) = 0
    · apply Or.inl
      change pantsStandardCapChart 0 ((u : ℂ) : ExtendedComplex) = ∞
      rw [hu, outerCapChart_zero]
    · apply Or.inr
      refine ⟨2 * (u : ℂ)⁻¹, ?_, (outerCapChart_coe _ hu).symm⟩
      have hprod : ‖2 * (u : ℂ)⁻¹‖ * ‖(u : ℂ)‖ = 2 := by
        rw [← norm_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]
        norm_num
      calc
        2 = ‖2 * (u : ℂ)⁻¹‖ * ‖(u : ℂ)‖ := hprod.symm
        _ ≤ ‖2 * (u : ℂ)⁻¹‖ * 1 :=
          mul_le_mul_of_nonneg_left u.norm_le_one (norm_nonneg _)
        _ = ‖2 * (u : ℂ)⁻¹‖ := mul_one _
  · intro p hp
    rcases hp with rfl | ⟨z, hz, rfl⟩
    · exact ⟨0, outerCapChart_zero⟩
    · change 2 ≤ ‖z‖ at hz
      have hz0 : z ≠ 0 := by intro he; subst z; norm_num at hz
      let u : ℂ := 2 * z⁻¹
      have hu0 : u ≠ 0 := mul_ne_zero (by norm_num) (inv_ne_zero hz0)
      have huz : u * z = 2 := by
        dsimp only [u]
        rw [mul_assoc, inv_mul_cancel₀ hz0, mul_one]
      have hprod : ‖u‖ * ‖z‖ = 2 := by rw [← norm_mul, huz]; norm_num
      have hub : ‖u‖ ≤ 1 := by
        have hbound := mul_le_mul_of_nonneg_left hz (norm_nonneg u)
        rw [hprod] at hbound
        linarith
      refine ⟨Complex.UnitClosedDisc.mk u hub, ?_⟩
      change pantsStandardCapChart 0 (u : ExtendedComplex) = (z : ExtendedComplex)
      rw [outerCapChart_coe _ hu0]
      apply congrArg (fun w : ℂ => (w : ExtendedComplex))
      calc
        2 * u⁻¹ = (u * z) * u⁻¹ := by rw [huz]
        _ = z * (u * u⁻¹) := by ring
        _ = z := by rw [mul_inv_cancel₀ hu0, mul_one]

private theorem halfAffine_closedDisc_range (b : ℂ) :
    range (fun u : Complex.UnitClosedDisc =>
      affineHomeomorph ((1 : ℂ) / 2) b (by norm_num) ((u : ℂ) : ExtendedComplex)) =
        (↑) '' {z : ℂ | ‖z - b‖ ≤ (1 : ℝ) / 2} := by
  apply subset_antisymm
  · rintro _ ⟨u, rfl⟩
    refine ⟨(1 / 2 : ℂ) * u + b, ?_, (affineHomeomorph_coe _ _ _ _).symm⟩
    change ‖(1 / 2 : ℂ) * (u : ℂ) + b - b‖ ≤ (1 : ℝ) / 2
    have he : (1 / 2 : ℂ) * u + b - b = (1 / 2 : ℂ) * u := by ring
    rw [he, norm_mul]
    have hu := u.norm_le_one
    have hn : ‖(1 / 2 : ℂ)‖ = (1 : ℝ) / 2 := by norm_num
    rw [hn]
    linarith
  · rintro _ ⟨z, hz, rfl⟩
    change ‖z - b‖ ≤ (1 : ℝ) / 2 at hz
    have hu : ‖(2 : ℂ) * (z - b)‖ ≤ 1 := by
      have hn : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      rw [norm_mul, hn]
      linarith
    refine ⟨Complex.UnitClosedDisc.mk (2 * (z - b)) hu, ?_⟩
    change affineHomeomorph ((1 : ℂ) / 2) b _
      ((2 * (z - b) : ℂ) : ExtendedComplex) = (z : ExtendedComplex)
    rw [affineHomeomorph_coe]
    apply congrArg (fun w : ℂ => (w : ExtendedComplex))
    ring

/-- The chart images are the full closed caps, including all their boundaries. -/
theorem pantsStandardCapChart_closedDisc_range (i : Fin 3) :
    range (fun z : Complex.UnitClosedDisc => pantsStandardCapChart i ((z : ℂ) : ExtendedComplex)) =
      pantsStandardExtendedCap i := by
  fin_cases i
  · exact outerCapChart_closedDisc_range
  · simpa [pantsStandardCapChart, pantsStandardExtendedCap, sub_neg_eq_add] using
      halfAffine_closedDisc_range (-1)
  · simpa [pantsStandardCapChart, pantsStandardExtendedCap] using halfAffine_closedDisc_range 1

/-- The actual sphere ranges are the exact images of these closed carriers. -/
theorem pantsStandardSphereCap_range (i : Fin 3) :
    range (pantsStandardSphereCap i) = pantsComplexSphereHomeomorph '' pantsStandardExtendedCap i := by
  change range (pantsComplexSphereHomeomorph ∘
    (fun z : Complex.UnitClosedDisc => pantsStandardCapChart i ((z : ℂ) : ExtendedComplex))) = _
  rw [range_comp, pantsStandardCapChart_closedDisc_range]

end LowDimensionalTopology.Geometry.Surfaces
