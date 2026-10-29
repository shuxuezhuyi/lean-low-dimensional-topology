module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairRecognizedSignature
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.ThreeEndCoreIsPants
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreCarrier

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Fuchsian

/-- The recognized annular group has a pants core and compact closed core on its own quotient. -/
theorem annularPair_originalCore_isPants_and_closedCore_compact
    (hRecognition : LowDimensionalTopology.Unproved.Fuchsian.AnnularPairBoundaryRecognition)
    (hDiscs : LowDimensionalTopology.Unproved.Surfaces.ThreeSphericalDiscs)
    (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E) :
    let P := (annularPairReflectionHalfPlaneData E r x hE hr hin hout).cayleyData
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    let hno := annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout
    Surfaces.IsHyperbolicPairOfPants (threeBoundaryQuotientModel P hno)
      (threeBoundaryOpenCore P hNE) ∧
      IsCompact (threeBoundaryClosedCore P hNE) := by
  dsimp only
  have hSig := annularPair_hasNielsenSignature_of_boundaryRecognition
    hRecognition E r x hE hr hin hout
  exact ⟨threeBoundaryOpenCore_isHyperbolicPairOfPants hDiscs hSig,
    isCompact_threeBoundaryClosedCore hSig⟩

end LowDimensionalTopology.Geometry.Hyperbolic
