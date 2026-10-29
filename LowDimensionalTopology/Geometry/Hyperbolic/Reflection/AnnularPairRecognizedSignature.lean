module

public import LowDimensionalTopology.Unproved.Fuchsian.AnnularPairBoundaryRecognition
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.ThreeBoundaryAreaSignature

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Fuchsian

/-- Actual boundary recognition and the core-area bound give the original group's signature. -/
theorem annularPair_hasNielsenSignature_of_boundaryRecognition
    (hRecognition : LowDimensionalTopology.Unproved.Fuchsian.AnnularPairBoundaryRecognition)
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    HasNielsenFuchsianSignature
      (annularPairReflectionHalfPlaneData E r x hE hr hin hout).cayleyData
      (annularPairReflectionDiscGroup_nonElementary E r x hE hr hin)
      (annularPairReflectionDiscGroup_fg E r x hE hr hin hout) 0 [] 0 3 := by
  let P := (annularPairReflectionHalfPlaneData E r x hE hr hin hout).cayleyData
  let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  let hFG := annularPairReflectionDiscGroup_fg E r x hE hr hin hout
  obtain ⟨hB, hArea⟩ := hRecognition E r x hE hr hin hout
  obtain ⟨w, hw, _⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  exact three_boundary_area_forces_signature P hNE hFG
    (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
    (annularBoundaryWordClass_three_le E r x hE hr hin hout hB)
    w hw (hArea w hw)

end LowDimensionalTopology.Geometry.Hyperbolic
