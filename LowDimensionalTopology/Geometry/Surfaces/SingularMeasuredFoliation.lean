module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.Homotopy.Basic

/-!
# Singular measured foliations in the original real smooth structure

The real smooth leaf charts preserve local plaques on overlaps. Singularities
have actual finite prong models. A transverse measure is an actual finite
Borel measure on each transverse arc, compatible with reparametrization,
restriction and leafwise isotopy. Nondegeneracy is a separate property.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal Topology Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]
variable {R : ClosedRiemannSurface X}

/-- Two actual local charts give the same local plaque partition near a point. -/
def LocallySamePlaques (e d : OpenPartialHomeomorph X ℂ) (p : X) : Prop :=
  ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ e.source ∩ d.source ∧
    ∀ x ∈ W, ∀ y ∈ W, (e x).im = (e y).im ↔ (d x).im = (d y).im

/-- A genuine local real smooth coordinate in the original surface structure. -/
def IsRealSmoothFoliationChart (R : ClosedRiemannSurface X)
    (e : OpenPartialHomeomorph X ℂ) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (e : X → ℂ) e.source ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (e.symm : ℂ → X) e.target

/-- A regular natural coordinate of the actual plane differential `phase * z^m dz²`. -/
def IsProngNaturalChart (m : ℕ) (phase : ℂ)
    (a : OpenPartialHomeomorph ℂ ℂ) : Prop :=
  0 ∉ a.source ∧ AnalyticOnNhd ℂ (a : ℂ → ℂ) a.source ∧
    ∀ z ∈ a.source, (deriv (a : ℂ → ℂ) z) ^ 2 = phase * z ^ m

/-- The actual leaves agree with the plane prong model through a real smooth local chart. -/
def MatchesProngModel (R : ClosedRiemannSurface X)
    (charts : Set (OpenPartialHomeomorph X ℂ))
    (m : ℕ) (phase : ℂ) (h : OpenPartialHomeomorph X ℂ) (p : X) : Prop :=
  IsRealSmoothFoliationChart R h ∧ p ∈ h.source ∧ h p = 0 ∧
    ∀ x ∈ h.source, x ≠ p →
      ∃ e ∈ charts, ∃ a : OpenPartialHomeomorph ℂ ℂ,
        IsProngNaturalChart m phase a ∧ LocallySamePlaques e (h.trans a) x

/-- A real smooth foliation atlas with a finite set of genuine isolated prong singularities. -/
structure SingularFoliationAtlas (R : ClosedRiemannSurface X) where
  singular : Set X
  singular_finite : singular.Finite
  charts : Set (OpenPartialHomeomorph X ℂ)
  chart_regular : ∀ e ∈ charts, e.source ⊆ singularᶜ
  chart_smooth : ∀ e ∈ charts, IsRealSmoothFoliationChart R e
  cover : ∀ x ∉ singular, ∃ e ∈ charts, x ∈ e.source
  compatible : ∀ e ∈ charts, ∀ d ∈ charts, ∀ p ∈ e.source ∩ d.source,
    LocallySamePlaques e d p
  prongs : ∀ p ∈ singular, ∃ m : ℕ, 0 < m ∧
    ∃ h : OpenPartialHomeomorph X ℂ,
      h.source ∩ singular = {p} ∧ MatchesProngModel R charts m 1 h p

/-- A genuine embedded regular arc crossing local plaques monotonically. -/
structure SingularFoliationAtlas.TransverseArc (A : SingularFoliationAtlas R) where
  curve : C(unitInterval, X)
  isEmbedding : Topology.IsEmbedding curve
  regular : ∀ t, curve t ∉ A.singular
  crosses : ∀ t : unitInterval, ∃ e ∈ A.charts, ∃ J : Set unitInterval,
    IsOpen J ∧ t ∈ J ∧ (∀ s ∈ J, curve s ∈ e.source) ∧
      (StrictMonoOn (fun s => (e (curve s)).im) J ∨
        StrictAntiOn (fun s => (e (curve s)).im) J)

/-- An isotopy through actual transverse arcs whose point tracks stay in local plaques. -/
def SingularFoliationAtlas.IsLeafwiseTransverseIsotopy
    (A : SingularFoliationAtlas R) (α β : A.TransverseArc)
    (H : ContinuousMap.Homotopy α.curve β.curve) : Prop :=
  (∀ s : unitInterval, ∃ γ : A.TransverseArc, ∀ t, γ.curve t = H (s, t)) ∧
    ∀ s t : unitInterval, ∃ e ∈ A.charts, ∃ J : Set unitInterval,
      IsOpen J ∧ s ∈ J ∧
        ∀ r ∈ J, H (r, t) ∈ e.source ∧ (e (H (r, t))).im = (e (H (s, t))).im

/-- Actual finite transverse measures compatible with subarcs, parameters and holonomy. -/
structure TransverseInvariantMeasure (A : SingularFoliationAtlas R) where
  measure : A.TransverseArc → Measure unitInterval
  finite : ∀ α, measure α univ < (∞ : ℝ≥0∞)
  reparametrize : ∀ (α β : A.TransverseArc) (ρ : unitInterval ≃ₜ unitInterval),
    (∀ t, β.curve t = α.curve (ρ t)) →
      Measure.map (ρ : unitInterval → unitInterval) (measure β) = measure α
  subarc : ∀ (α β : A.TransverseArc) (a b : unitInterval), a < b →
    ∀ σ : C(unitInterval, unitInterval),
      (∀ t, (σ t : ℝ) = (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)) →
      (∀ t, β.curve t = α.curve (σ t)) →
      Measure.map (σ : unitInterval → unitInterval) (measure β) =
        (measure α).restrict (Icc a b)
  holonomy : ∀ (α β : A.TransverseArc) (H : ContinuousMap.Homotopy α.curve β.curve),
    A.IsLeafwiseTransverseIsotopy α β H → measure α = measure β

/-- A foliation and an actual transverse measure in the unchanged real smooth structure. -/
structure SingularMeasuredFoliation (R : ClosedRiemannSurface X) where
  atlas : SingularFoliationAtlas R
  transverse : TransverseInvariantMeasure atlas

/-- Every actual transverse arc has an atomless measure with full support. -/
def SingularMeasuredFoliation.IsNondegenerate (F : SingularMeasuredFoliation R) : Prop :=
  ∀ α : F.atlas.TransverseArc,
    (∀ t : unitInterval, F.transverse.measure α {t} = 0) ∧
      ∀ U : Set unitInterval, IsOpen U → U.Nonempty → 0 < F.transverse.measure α U

/-- A transverse pair has real smooth product charts and a common alternating prong model. -/
def AreTransverseMeasuredFoliations (F G : SingularMeasuredFoliation R) : Prop :=
  F.atlas.singular = G.atlas.singular ∧
    (∀ p ∉ F.atlas.singular,
      ∃ e ∈ F.atlas.charts, ∃ d ∈ G.atlas.charts,
        ∃ h : OpenPartialHomeomorph X ℂ,
          IsRealSmoothFoliationChart R h ∧ p ∈ h.source ∧
            h.source ⊆ e.source ∩ d.source ∧
            ∀ x ∈ h.source, h x = Complex.mk (e x).im (d x).im) ∧
    ∀ p ∈ F.atlas.singular, ∃ m : ℕ, 0 < m ∧
      ∃ h : OpenPartialHomeomorph X ℂ,
        h.source ∩ F.atlas.singular = {p} ∧
          MatchesProngModel R F.atlas.charts m 1 h p ∧
          MatchesProngModel R G.atlas.charts m (-1) h p

/-- A homeomorphism preserving local leaves and scaling every actual transverse measure. -/
def IsMeasuredFoliationHomothety (F : SingularMeasuredFoliation R)
    (f : X ≃ₜ X) (c : ℝ) : Prop :=
  0 < c ∧ f '' F.atlas.singular = F.atlas.singular ∧
    (∀ p ∉ F.atlas.singular,
      ∃ e ∈ F.atlas.charts, ∃ d ∈ F.atlas.charts,
        ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ e.source ∩ f ⁻¹' d.source ∧
          ∀ x ∈ W, ∀ y ∈ W,
            (e x).im = (e y).im ↔ (d (f x)).im = (d (f y)).im) ∧
    (∀ α : F.atlas.TransverseArc, ∃ β : F.atlas.TransverseArc,
      ∀ t, β.curve t = f (α.curve t)) ∧
    (∀ β : F.atlas.TransverseArc, ∃ α : F.atlas.TransverseArc,
      ∀ t, β.curve t = f (α.curve t)) ∧
    ∀ α β : F.atlas.TransverseArc, (∀ t, β.curve t = f (α.curve t)) →
      F.transverse.measure β = ENNReal.ofReal c • F.transverse.measure α

end LowDimensionalTopology.Geometry.Surfaces
