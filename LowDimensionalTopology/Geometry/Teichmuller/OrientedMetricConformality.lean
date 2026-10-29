module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricEquivalence

/-!
# Conformal maps between original oriented Riemannian surfaces

The two surfaces and their full smooth metrics are independent. A conformal
map preserves orientation and pulls the actual target metric back to a smooth
exponential multiple of the actual source metric, on both original tangent
slots. No compatibility with the reference complex atlases is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v w
variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {R : RiemannSurface X} {S : RiemannSurface Y} {T : RiemannSurface Z}

/-- A positive actual diffeomorphism satisfying the full metric pullback equation. -/
def IsOrientedMetricConformal (g : SmoothSurfaceMetric R) (h : SmoothSurfaceMetric S)
    (f : SmoothSurfaceEquiv R S) : Prop :=
  PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph ∧
    IsRawMetricConformal g h f

/-- Existence of an actual orientation-preserving conformal diffeomorphism. -/
def OrientedMetricEquivalent (g : SmoothSurfaceMetric R) (h : SmoothSurfaceMetric S) : Prop :=
  ∃ f : SmoothSurfaceEquiv R S, IsOrientedMetricConformal g h f

namespace IsOrientedMetricConformal

theorem refl (g : SmoothSurfaceMetric R) :
    IsOrientedMetricConformal g g (SmoothSurfaceEquiv.refl R) :=
  ⟨preservesComplexOrientation_id R.toRiemannAtlas, IsRawMetricConformal.refl g⟩

theorem symm {g : SmoothSurfaceMetric R} {h : SmoothSurfaceMetric S}
    {f : SmoothSurfaceEquiv R S} (hf : IsOrientedMetricConformal g h f) :
    IsOrientedMetricConformal h g (SmoothSurfaceEquiv.symm f) :=
  ⟨PreservesComplexOrientation.homeomorph_symm f.toHomeomorph hf.1,
    IsRawMetricConformal.symm hf.2⟩

theorem trans {g : SmoothSurfaceMetric R} {h : SmoothSurfaceMetric S}
    {k : SmoothSurfaceMetric T} {f : SmoothSurfaceEquiv R S}
    {j : SmoothSurfaceEquiv S T} (hf : IsOrientedMetricConformal g h f)
    (hj : IsOrientedMetricConformal h k j) :
    IsOrientedMetricConformal g k (SmoothSurfaceEquiv.trans f j) :=
  ⟨hj.1.comp hf.1 f.toHomeomorph.continuous, IsRawMetricConformal.trans hf.2 hj.2⟩

/-- The genuine pullback of any target metric makes the same positive map conformal. -/
theorem pullback (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (h : SmoothSurfaceMetric S) :
    IsOrientedMetricConformal (SmoothSurfaceMetric.pullback f h) h f :=
  ⟨hf, IsRawMetricConformal.pullback f h⟩

end IsOrientedMetricConformal

namespace OrientedMetricEquivalent

theorem refl (g : SmoothSurfaceMetric R) : OrientedMetricEquivalent g g :=
  ⟨SmoothSurfaceEquiv.refl R, IsOrientedMetricConformal.refl g⟩

theorem symm {g : SmoothSurfaceMetric R} {h : SmoothSurfaceMetric S}
    (hgh : OrientedMetricEquivalent g h) : OrientedMetricEquivalent h g := by
  obtain ⟨f, hf⟩ := hgh
  exact ⟨SmoothSurfaceEquiv.symm f, IsOrientedMetricConformal.symm hf⟩

theorem trans {g : SmoothSurfaceMetric R} {h : SmoothSurfaceMetric S}
    {k : SmoothSurfaceMetric T} (hgh : OrientedMetricEquivalent g h)
    (hhk : OrientedMetricEquivalent h k) : OrientedMetricEquivalent g k := by
  obtain ⟨f, hf⟩ := hgh
  obtain ⟨j, hj⟩ := hhk
  exact ⟨SmoothSurfaceEquiv.trans f j, IsOrientedMetricConformal.trans hf hj⟩

end OrientedMetricEquivalent

/-- On a closed reference, the general map predicate retains the exact existing relation. -/
theorem isOrientedMetricConformal_iff_rawMetricConformal
    (R : ClosedRiemannSurface X) (g h : SmoothSurfaceMetric R.toRiemannSurface)
    (f : OrientedSurfaceAut R) :
    IsOrientedMetricConformal g h f.smooth ↔ RawMetricConformal R g h f :=
  ⟨And.right, fun hf => ⟨f.orientation_preserving, hf⟩⟩

/-- The original full closed-reference quotient uses exactly this general conformal relation. -/
theorem orientedMetricEquivalent_iff_rawMetricEquivalent
    (R : ClosedRiemannSurface X) (g h : SmoothSurfaceMetric R.toRiemannSurface) :
    OrientedMetricEquivalent g h ↔ RawMetricEquivalent R g h := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨⟨f, hf.1⟩, hf.2⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.smooth, f.orientation_preserving, hf⟩

end LowDimensionalTopology.Geometry.Teichmuller
