module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularBoundaryClassInjection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairNonElementary
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreArea

@[expose] public section
noncomputable section

namespace LowDimensionalTopology.Unproved.Fuchsian
open LowDimensionalTopology.Geometry
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Fuchsian

/-- The strict original three-mirror group has its three literal boundary words
and the doubled-chamber Nielsen area bound. This proposition is unproved here. -/
def AnnularPairBoundaryRecognition : Prop :=
  ∀ (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (hin : 1 + r < x) (hout : x + r < E),
    let P := (annularPairReflectionHalfPlaneData E r x hE hr hin hout).cayleyData
    let hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
    (∀ i : Fin 3, IsBoundaryHyperbolic P.asFuchsianDisc
      (annularDiscPeripheralWord E r x hE hr hin hout i)) ∧
    ∀ (w : P.domain.carrier), IsDirichletCenter P w →
      fuchsianNielsenCoreArea P hNE (dirichletDomain P w) ≤
        ENNReal.ofReal (2 * Real.pi)

end LowDimensionalTopology.Unproved.Fuchsian
