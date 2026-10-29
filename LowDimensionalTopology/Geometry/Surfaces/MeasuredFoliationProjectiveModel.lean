module

public import LowDimensionalTopology.Geometry.Surfaces.MeasuredFoliationIntersectionHomogeneity
public import LowDimensionalTopology.Geometry.Surfaces.ProjectiveSpectrumClosure

/-!
# The actual projective measured-foliation coordinate model

The common-scaling quotient maps by its actual intersection ray into the
original projective curve boundary. Injectivity and surjectivity concern that
same map, with every geometric input retained explicitly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable (hCurve : Unproved.Surfaces.ClosedCurveIntersectionGeometry R hg hgenus)
variable (H : Unproved.Surfaces.OriginalMeasuredFoliationIntersectionGeometry R hg hgenus hCurve)

/-- The actual intersection ray lies in the original projective curve-spectrum closure. -/
def projectiveMeasuredFoliationBoundaryMap
    (q : ProjectiveNondegenerateMeasuredFoliationQuotient R) :
    originalThurstonBoundary R hg hgenus hCurve := by
  refine ⟨projectiveMeasuredFoliationIntersectionSpectrum R hg hgenus hCurve H q, ?_⟩
  refine Quotient.inductionOn q ?_
  intro z
  change projectivizeNonnegativeSpectrum
    (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H z) ∈ _
  apply (projectivizeNonnegativeSpectrum_mem_originalThurstonBoundary_iff
    R hg hgenus hCurve _).mpr
  exact (measuredFoliationIntersectionConeMap R hg hgenus hCurve H z).property

/-- The boundary value retains the exact original measured-foliation representative. -/
theorem projectiveMeasuredFoliationBoundaryMap_mk
    (q : NondegenerateMeasuredFoliationQuotient R) :
    (projectiveMeasuredFoliationBoundaryMap R hg hgenus hCurve H
      (projectivizeNondegenerateMeasuredFoliation q)).val =
        projectivizeNonnegativeSpectrum
          (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q) := rfl

/-- Equal actual rays give one common positive scale in the original geometric quotient. -/
theorem projectiveMeasuredFoliationBoundaryMap_injective :
    Function.Injective (projectiveMeasuredFoliationBoundaryMap R hg hgenus hCurve H) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y hxy
  have hray := congrArg Subtype.val hxy
  change projectivizeNonnegativeSpectrum
    (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H x) =
      projectivizeNonnegativeSpectrum
        (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H y) at hray
  obtain ⟨c, hc, hcoords⟩ := (projectivizeNonnegativeSpectrum_eq_iff _ _).mp hray
  have hprofile : measuredFoliationIntersectionSpectrum R hg hgenus hCurve H x =
      measuredFoliationIntersectionSpectrum R hg hgenus hCurve H
        (scaleNondegenerateMeasuredFoliationQuotient ⟨c, hc⟩ y) := by
    apply Subtype.ext
    funext β
    apply Subtype.ext
    exact (hcoords β).trans
      (measuredFoliationIntersectionSpectrum_scale R hg hgenus hCurve H ⟨c, hc⟩ y β).symm
  have hclasses : x = scaleNondegenerateMeasuredFoliationQuotient ⟨c, hc⟩ y := by
    apply measuredFoliationIntersectionConeMap_injective R hg hgenus hCurve H
    apply Subtype.ext
    exact hprofile
  apply Quotient.sound
  exact Relation.EqvGen.symm y x (Relation.EqvGen.rel y x ⟨⟨c, hc⟩, hclasses⟩)

/-- Every original boundary ray is represented by an actual geometric foliation class. -/
theorem projectiveMeasuredFoliationBoundaryMap_surjective :
    Function.Surjective (projectiveMeasuredFoliationBoundaryMap R hg hgenus hCurve H) := by
  intro p
  obtain ⟨f, hf⟩ := (isQuotientMap_projectivizeNonnegativeSpectrum (X := X)).surjective p.val
  have hfp : projectivizeNonnegativeSpectrum f ∈
      originalThurstonBoundary R hg hgenus hCurve := hf.symm ▸ p.property
  have hclosure := (projectivizeNonnegativeSpectrum_mem_originalThurstonBoundary_iff
    R hg hgenus hCurve f).mp hfp
  obtain ⟨q, hq⟩ := measuredFoliationIntersectionConeMap_surjective R hg hgenus hCurve H
    ⟨f, hclosure⟩
  refine ⟨projectivizeNondegenerateMeasuredFoliation q, ?_⟩
  apply Subtype.ext
  change projectivizeNonnegativeSpectrum
    (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q) = p.val
  calc
    projectivizeNonnegativeSpectrum
        (measuredFoliationIntersectionSpectrum R hg hgenus hCurve H q) =
      projectivizeNonnegativeSpectrum f :=
        congrArg (fun z : OriginalMeasuredFoliationSpectrumCone R hg hgenus hCurve =>
          projectivizeNonnegativeSpectrum z.val) hq
    _ = p.val := hf

/-- The conditional equivalence is induced by the actual measured-intersection ray map. -/
def projectiveMeasuredFoliationBoundaryEquiv :
    ProjectiveNondegenerateMeasuredFoliationQuotient R ≃
      originalThurstonBoundary R hg hgenus hCurve :=
  Equiv.ofBijective (projectiveMeasuredFoliationBoundaryMap R hg hgenus hCurve H)
    ⟨projectiveMeasuredFoliationBoundaryMap_injective R hg hgenus hCurve H,
      projectiveMeasuredFoliationBoundaryMap_surjective R hg hgenus hCurve H⟩

end LowDimensionalTopology.Geometry.Surfaces
