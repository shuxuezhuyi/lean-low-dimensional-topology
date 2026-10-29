module

public import LowDimensionalTopology.Geometry.Polygon.Hexagon.HexagonPolygonAdapters
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.BoundaryReflectionExactDistance

/-!
# Exact reflection shifts from an actual right hexagon

The matrix is the product of the two genuine neighbouring mirror reflections.
Its normalized shift is twice the actual intervening edge length. This does
not assert existence of a hexagon for prescribed input lengths or a quotient
group/signature for this reflection subgroup.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Fuchsian

/-- The actual adjacent-mirror product has normalized shift twice the actual
edge distance, on every native upper-half-plane point. -/
theorem RightHexagon.edge_reflection_translation (Q : RightHexagon) (i : Fin 6) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      0 < 2 * Q.edgeLength i ∧
      q • Q.vertex i = UpperHalfPlane.I ∧
      q • (Q.side (i + 1)).reflection (Q.vertex i) =
        imaginaryAxisParam (2 * Q.edgeLength i) ∧
      (Q.side i).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ q) = HalfPlaneLine.vertical 0 ∧
      ∀ z : ℍ, q • (reflectionProductSL (Q.side (i + 1)) (Q.side (i - 1)) • z) =
        signatureBoundaryShift (2 * Q.edgeLength i) (q • z) := by
  let R := Q.side (i - 1)
  let M := Q.side (i + 1)
  let K := Q.side i
  let u := Q.vertex i
  let d := Q.vertex (i + 1)
  have hR : R.OrthogonalAt K u := by
    simpa only [R, K, u, sub_add_cancel] using Q.right_angle (i - 1)
  have hM : M.OrthogonalAt K d := by
    have hh := Q.right_angle i
    exact ⟨hh.2.1, hh.1, by rw [real_inner_comm]; exact hh.2.2⟩
  have hu : u ∈ K.carrier := Q.side_contains_vertex i
  have hid : i ≠ i + 1 := by fin_cases i <;> decide
  have hud : u ≠ d := Q.vertex_injective.ne hid
  have hv : M.reflection u ∈ K.carrier :=
    M.reflection_image_of_orthogonalAt K d hM ▸ mem_image_of_mem M.reflection hu
  have huv : u ≠ M.reflection u :=
    (M.reflection_ne_of_perpendicular K d u hM hu hud).symm
  have hlength : dist u (M.reflection u) = 2 * Q.edgeLength i :=
    (M.reflection_perpendicular_midpoint K d u hM hu hud).2
  obtain ⟨q, hpos, hqu, hqv, hK, hact⟩ :=
    generalSignature_boundary_reflection_translation_exact_distance
      R M K u (M.reflection u) huv hR hv rfl
  refine ⟨q, ?_, hqu, ?_, hK, ?_⟩
  · simpa only [hlength] using hpos
  · simpa only [hlength] using hqv
  · simpa only [reflectionProductSL_action, hlength] using hact

end LowDimensionalTopology.Geometry.Polygon
