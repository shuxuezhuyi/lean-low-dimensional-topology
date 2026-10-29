module

public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBoundaryTranslation

@[expose] public section
noncomputable section
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual reflection product is conjugate to the shift by the exact
distance from the fixed first-mirror point to its second-mirror image. -/
theorem generalSignature_boundary_reflection_translation_exact_distance
    (R M K : HalfPlaneLine) (u v : ℍ) (huv : u ≠ v)
    (hR : R.OrthogonalAt K u) (hv : v ∈ K.carrier)
    (hM : M.reflection u = v) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      0 < dist u v ∧
      q • u = UpperHalfPlane.I ∧
      q • v = imaginaryAxisParam (dist u v) ∧
      K.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q) = HalfPlaneLine.vertical 0 ∧
      ∀ z : ℍ, q • M.reflection (R.reflection z) =
        signatureBoundaryShift (dist u v) (q • z) := by
  obtain ⟨q, l, hl, hqu, hqv, hK, ht⟩ :=
    generalSignature_boundary_reflection_translation R M K u v huv hR hv hM
  have hI : UpperHalfPlane.I = imaginaryAxisParam 0 := by
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [imaginaryAxisParam, UpperHalfPlane.I]
  have hd : dist u v = l := by
    calc
      dist u v = dist (q • u) (q • v) :=
        ((isometry_smul ℍ q).dist_eq u v).symm
      _ = dist (imaginaryAxisParam 0) (imaginaryAxisParam l) := by
        rw [hqu, hqv, hI]
      _ = dist (0 : ℝ) l := imaginaryAxisParam_isometry.dist_eq 0 l
      _ = l := by rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hl]
  refine ⟨q, ?_, hqu, ?_, hK, ?_⟩
  · simpa only [hd] using hl
  · simpa only [hd] using hqv
  · simpa only [hd] using ht

end LowDimensionalTopology.Geometry.Fuchsian
