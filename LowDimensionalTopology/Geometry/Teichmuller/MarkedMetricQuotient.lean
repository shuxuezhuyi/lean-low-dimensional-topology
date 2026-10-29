module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricEquivalence

/-!
# Natural marked-surface maps into the full raw metric quotients

The metric is pulled back from the actual marked target by the same original
marking. An actual biholomorphic change of target gives a conformal reference
automorphism. Compatibility of markings up to homotopy puts that automorphism
in the existing Diff₀ subgroup. Conversely a strong conformal witness between
these pullback metrics gives a biholomorphic target change by the proved
metric-conformality theorem. Thus the natural map on Teichmüller classes is
injective. Surjectivity onto all raw metric classes is not proved here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The actual reference automorphism obtained by conjugating a given
biholomorphic change of marked target by the two actual markings. -/
def metricComparisonAut (M N : MarkedRiemannSurface.{u, v} R)
    (h : M.carrier ≃ₜ N.carrier)
    (han : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    OrientedSurfaceAut R where
  smooth := SmoothSurfaceEquiv.trans
    (SmoothSurfaceEquiv.trans M.marking
      (SmoothSurfaceEquiv.ofConformalHomeomorph
        M.surface.toRiemannSurface N.surface.toRiemannSurface h han))
    (SmoothSurfaceEquiv.symm N.marking)
  orientation_preserving :=
    (PreservesComplexOrientation.homeomorph_symm N.marking.toHomeomorph
      N.orientation_preserving).comp
      ((analyticHomeomorph_preservesComplexOrientation h han).comp
        M.orientation_preserving M.marking.toHomeomorph.continuous)
      (h.continuous.comp M.marking.toHomeomorph.continuous)

/-- The conjugated actual automorphism is conformal between the two actual
pullback metrics, using the existing compatible metrics on their own targets. -/
theorem metricComparisonAut_conformal (M N : MarkedRiemannSurface.{u, v} R)
    (h : M.carrier ≃ₜ N.carrier)
    (han : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    RawMetricConformal R M.correspondingMetric N.correspondingMetric
      (metricComparisonAut M N h han) := by
  let f := SmoothSurfaceEquiv.ofConformalHomeomorph
    M.surface.toRiemannSurface N.surface.toRiemannSurface h han
  have hf : IsMetricConformal M.compatibleTargetMetric N.compatibleTargetMetric f :=
    AtlasInducedMetric.metricConformal_of_analytic
      M.compatibleTargetMetric N.compatibleTargetMetric f han
  exact ((IsRawMetricConformal.pullback M.marking M.compatibleTargetMetric.metric).trans
    hf.raw).trans
      (IsRawMetricConformal.pullback N.marking N.compatibleTargetMetric.metric).symm

/-- The actual marked homotopy puts the conjugated reference automorphism
in the actual homotopy-identity subgroup. -/
theorem metricComparisonAut_mem_homotopyIdentity
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (han : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h)
    (hmark : ContinuousMap.Homotopic
      ((_root_.toContinuousMap h).comp M.markingMap) N.markingMap) :
    metricComparisonAut M N h han ∈ OrientedSurfaceAut.homotopyIdentitySubgroup R := by
  change ContinuousMap.Homotopic (metricComparisonAut M N h han).continuousMap
    (ContinuousMap.id X)
  have hc := (ContinuousMap.Homotopic.refl
    (_root_.toContinuousMap N.marking.toHomeomorph.symm)).comp hmark
  have hleft : (_root_.toContinuousMap N.marking.toHomeomorph.symm).comp
      ((_root_.toContinuousMap h).comp M.markingMap) =
      (metricComparisonAut M N h han).continuousMap := by
    ext x
    rfl
  have hright : (_root_.toContinuousMap N.marking.toHomeomorph.symm).comp N.markingMap =
      ContinuousMap.id X := by
    ext x
    exact N.marking.toHomeomorph.symm_apply_apply x
  rw [hleft, hright] at hc
  exact hc

/-- A biholomorphic target change gives weak equivalence of the actual raw
pullback metrics, independently of the marked homotopy condition. -/
theorem correspondingMetric_equivalent_of_analytic_target
    (M N : MarkedRiemannSurface.{u, v} R) (h : M.carrier ≃ₜ N.carrier)
    (han : RiemannAnalyticMap M.surface.toRiemannAtlas N.surface.toRiemannAtlas h) :
    RawMetricEquivalent R M.correspondingMetric N.correspondingMetric :=
  ⟨metricComparisonAut M N h han, metricComparisonAut_conformal M N h han⟩

/-- Equivalent actual markings have strongly equivalent raw pullback metrics. -/
theorem correspondingMetric_stronglyEquivalent
    {M N : MarkedRiemannSurface.{u, v} R} (hMN : Equivalent M N) :
    RawMetricStronglyEquivalent R M.correspondingMetric N.correspondingMetric := by
  obtain ⟨h, han, hmark⟩ := hMN
  exact ⟨metricComparisonAut M N h han,
    metricComparisonAut_mem_homotopyIdentity M N h han hmark,
    metricComparisonAut_conformal M N h han⟩

/-- A strong raw conformal witness between the actual marking pullbacks
recovers the original marked-surface equivalence. The target map is the actual
composition `N.marking ∘ a ∘ M.marking⁻¹`. -/
theorem equivalent_of_correspondingMetric_stronglyEquivalent
    {M N : MarkedRiemannSurface.{u, v} R}
    (hMN : RawMetricStronglyEquivalent R M.correspondingMetric N.correspondingMetric) :
    Equivalent M N := by
  let := R.toRiemannAtlas.toChartedSpace
  let := M.surface.toRiemannAtlas.toChartedSpace
  let := N.surface.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := M.surface.toRiemannAtlas.isRealManifold
  let := N.surface.toRiemannAtlas.isRealManifold
  obtain ⟨a, haid, ha⟩ := hMN
  let f := SmoothSurfaceEquiv.trans
    (SmoothSurfaceEquiv.trans (SmoothSurfaceEquiv.symm M.marking) a.smooth) N.marking
  have hf : PreservesComplexOrientation M.surface.toRiemannAtlas
      N.surface.toRiemannAtlas f.toHomeomorph :=
    N.orientation_preserving.comp
      (a.orientation_preserving.comp
        (PreservesComplexOrientation.homeomorph_symm M.marking.toHomeomorph
          M.orientation_preserving) M.marking.toHomeomorph.symm.continuous)
      (a.toHomeomorph.continuous.comp M.marking.toHomeomorph.symm.continuous)
  have hconf : IsMetricConformal M.compatibleTargetMetric N.compatibleTargetMetric f :=
    (((IsRawMetricConformal.pullback M.marking M.compatibleTargetMetric.metric).symm).trans
      ha).trans
        (IsRawMetricConformal.pullback N.marking N.compatibleTargetMetric.metric)
  have han := AtlasInducedMetric.analytic_of_metricConformal
    M.compatibleTargetMetric N.compatibleTargetMetric f hf hconf
  refine ⟨f.toHomeomorph, han, ?_⟩
  change ContinuousMap.Homotopic a.continuousMap (ContinuousMap.id X) at haid
  have hc := (ContinuousMap.Homotopic.refl N.markingMap).comp haid
  have heq : (_root_.toContinuousMap f.toHomeomorph).comp M.markingMap =
      N.markingMap.comp a.continuousMap := by
    ext x
    change N.marking.toHomeomorph
      (a.toHomeomorph (M.marking.toHomeomorph.symm (M.marking.toHomeomorph x))) =
      N.marking.toHomeomorph (a.toHomeomorph x)
    rw [M.marking.toHomeomorph.symm_apply_apply]
  rw [heq]
  exact hc

/-- On actual marking pullbacks, strong raw conformal equivalence is exactly
the already defined marked complex-structure equivalence. -/
theorem correspondingMetric_stronglyEquivalent_iff
    (M N : MarkedRiemannSurface.{u, v} R) :
    RawMetricStronglyEquivalent R M.correspondingMetric N.correspondingMetric ↔
      Equivalent M N :=
  ⟨equivalent_of_correspondingMetric_stronglyEquivalent,
    correspondingMetric_stronglyEquivalent⟩

end MarkedRiemannSurface

namespace TeichmullerSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The natural map takes a marked complex structure to the strong conformal
class of its actual raw pullback metric. -/
def toRawMetricStrongQuotient : TeichmullerSpace.{u, v} R → RawMetricStrongQuotient R :=
  Quotient.lift (fun M => RawMetricStrongQuotient.mk M.correspondingMetric) (by
    intro M N hMN
    exact Quotient.sound (MarkedRiemannSurface.correspondingMetric_stronglyEquivalent hMN))

@[simp]
theorem toRawMetricStrongQuotient_mk (M : MarkedRiemannSurface.{u, v} R) :
    toRawMetricStrongQuotient (mk M) = RawMetricStrongQuotient.mk M.correspondingMetric := rfl

/-- Equality of strong metric classes recovers the original Teichmüller point.
This is an injection into the full raw metric quotient, with no realizability
restriction on the latter's type. -/
theorem toRawMetricStrongQuotient_injective :
    Function.Injective (toRawMetricStrongQuotient.{u, v} (R := R)) := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro M N hMN
  apply Quotient.sound
  apply MarkedRiemannSurface.equivalent_of_correspondingMetric_stronglyEquivalent
  exact Quotient.exact hMN

/-- The corresponding natural weak class map forgets the Diff₀ restriction. -/
def toRawMetricQuotient : TeichmullerSpace.{u, v} R → RawMetricQuotient R :=
  RawMetricStrongQuotient.toWeak ∘ toRawMetricStrongQuotient

@[simp]
theorem toRawMetricQuotient_mk (M : MarkedRiemannSurface.{u, v} R) :
    toRawMetricQuotient (mk M) = RawMetricQuotient.mk M.correspondingMetric := rfl

end TeichmullerSpace
end LowDimensionalTopology.Geometry.Teichmuller
