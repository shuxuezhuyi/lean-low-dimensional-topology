/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.GeneralMulticurve
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicPantsDecomposition
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.PantsNielsenExtension
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableCurves
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.CyclicHyperbolicAnnulus
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.ParabolicCusps
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.PantsQuotientModel
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import Mathlib.Order.Minimal
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Hubbard decompositions extending a prescribed finite family

A finite geodesic multicurve extends to a maximal family whose intrinsically
completed complementary pieces are generalized pants, finite half-annuli or
closed hyperbolic half-planes. Every component of the closure of the curve
union minus the union is a simple complete geodesic bounding one such half-plane.

All pieces retain the original metric and exact lift stabilizer. Relative
closure is taken inside the open disc before embedding into the sphere.
Cusp and funnel ideal points remain absent from the completed cut carrier.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped unitInterval ENNReal

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Hyperbolic Geometry.Mobius Geometry.Fuchsian

variable {X : Type} [TopologicalSpace X] {R : RiemannSurface X}

/-- The actual union, without adding accumulation curves. -/
def hubbardCurveUnion (Y : Set (EssentialSimpleCircle X)) : Set X :=
  ⋃ c ∈ Y, Set.range c.val

/-- Every component of the complement of the closure of the actual union. -/
def hubbardPieces (Y : Set (EssentialSimpleCircle X)) : Set (Set X) :=
  geodesicComplementComponents ({closure (hubbardCurveUnion Y)} : Set (Set X))

/-- Every component of closure(union) minus union, including all limit leaves. -/
def hubbardResidualComponents (Y : Set (EssentialSimpleCircle X)) : Set (Set X) :=
  {D | ∃ x ∈ closure (hubbardCurveUnion Y) \ hubbardCurveUnion Y,
    connectedComponentIn (closure (hubbardCurveUnion Y) \ hubbardCurveUnion Y) x = D}

abbrev HubbardPieceIndex (Y : Set (EssentialSimpleCircle X)) :=
  {P : Set X // P ∈ hubbardPieces Y}

/-- Infimum of all original-atlas BV lengths with the specified endpoints,
using curves contained in the same subset. -/
def hubbardPieceLengthInf (M : HyperbolicSurfaceModel R) (P : Set X) (a b : P) : ℝ≥0∞ :=
  ⨅ c : RiemannSurfaceRectifiableCurvePiece R,
    ⨅ (_h0 : c.curve 0 = a.val) (_h1 : c.curve 1 = b.val)
      (_hP : ∀ t : I, c.curve t ∈ P), M.rectifiableCurveLength c

/-- Closure in the actual OPEN hyperbolic disc, not in ExtendedComplex. -/
def hubbardClosedLift (M : HyperbolicSurfaceModel R) (P : Set X)
    (s : M.discCover ⁻¹' P) : Set extendedUnitDisc :=
  closure (connectedComponentIn (M.discCover ⁻¹' P) s.val)

/-- Embed only the preceding relative closure into the sphere. -/
def hubbardClosedLiftSphere (M : HyperbolicSurfaceModel R) (P : Set X)
    (s : M.discCover ⁻¹' P) : Set ExtendedComplex :=
  Subtype.val '' hubbardClosedLift M P s

/-- The closed lift modulo its exact stabilizer, retaining distinct cut sides. -/
abbrev HubbardCut (M : HyperbolicSurfaceModel R) (P : Set X) (s : M.discCover ⁻¹' P) :=
  Geometry.DiscreteGroups.Action.restrictedOrbitQuotient
    (pantsNielsenStabilizer M P s) ExtendedComplex (hubbardClosedLiftSphere M P s)

/-- The actual class of every point of the relative closed lift. -/
def hubbardCutProjection (M : HyperbolicSurfaceModel R) (P : Set X)
    (s : M.discCover ⁻¹' P) (w : hubbardClosedLift M P s) : HubbardCut M P s :=
  Geometry.DiscreteGroups.Action.restrictedProjection
    (pantsNielsenStabilizer M P s) ExtendedComplex (hubbardClosedLiftSphere M P s)
      ⟨w.val.val, ⟨w.val, w.property, rfl⟩⟩

/-- The same projection restricted to the original open lift. -/
def hubbardOpenCutProjection (M : HyperbolicSurfaceModel R) (P : Set X)
    (s : M.discCover ⁻¹' P)
    (u : connectedComponentIn (M.discCover ⁻¹' P) s.val) : HubbardCut M P s :=
  hubbardCutProjection M P s ⟨u.val, subset_closure u.property⟩

/-- A faithful completion certificate on the literal closed-lift quotient.
Its metric, completeness and length identity are conclusions, not inputs. -/
structure HubbardCutCompletion (M : HyperbolicSurfaceModel R) (P : Set X)
    (s : M.discCover ⁻¹' P) where
  metric : MetricSpace (HubbardCut M P s)
  topology_eq : metric.toUniformSpace.toTopologicalSpace =
    TopologicalSpace.coinduced
      (Geometry.DiscreteGroups.Action.restrictedProjection
        (pantsNielsenStabilizer M P s) ExtendedComplex (hubbardClosedLiftSphere M P s))
      (inferInstance : TopologicalSpace (hubbardClosedLiftSphere M P s))
  complete : @CompleteSpace (HubbardCut M P s) metric.toUniformSpace
  inclusion : P → HubbardCut M P s
  inclusion_open : IsOpenEmbedding inclusion
  inclusion_dense : DenseRange inclusion
  inclusion_range : Set.range inclusion = Set.range (hubbardOpenCutProjection M P s)
  projection : C(HubbardCut M P s, X)
  projection_lift : ∀ w : hubbardClosedLift M P s,
    projection (hubbardCutProjection M P s w) = M.discCover w.val
  inclusion_lift : ∀ u : connectedComponentIn (M.discCover ⁻¹' P) s.val,
    inclusion ⟨M.discCover u.val,
      connectedComponentIn_subset (M.discCover ⁻¹' P) s.val u.property⟩ =
        hubbardOpenCutProjection M P s u
  projection_inclusion : ∀ a : P, projection (inclusion a) = a.val
  distance_original : ∀ a b : P,
    (letI := metric; edist (inclusion a) (inclusion b)) = hubbardPieceLengthInf M P a b

/-- Restrict the actual original action to the selected lift stabilizer. -/
theorem hubbardCutDiscGroup (M : HyperbolicSurfaceModel R) (P : Set X)
    (s : M.discCover ⁻¹' P) : UnitDiscFuchsianGroup (pantsNielsenStabilizer M P s) :=
  { invariant := (pantsNielsenExtensionDomain M P s).invariant
    discontinuous := restrictMobiusDomain_discontinuous
      (unitDiscMobiusInvariantDomain M.group M.invariant) (pantsNielsenStabilizer M P s)
      (mobiusSetStabilizer_le M.group (pantsNielsenLiftCarrier M P s)) M.discontinuous }

/-- Its genuine quotient model inherits absence of elliptics from the SAME M. -/
def hubbardCutQuotientModel (M : HyperbolicSurfaceModel R) (P : Set X)
    (s : M.discCover ⁻¹' P) :
    HyperbolicSurfaceModel (threeBoundaryQuotientRiemannSurface (hubbardCutDiscGroup M P s)) :=
  threeBoundaryQuotientModel (hubbardCutDiscGroup M P s)
    (fun f hf hne => M.no_elliptic f
      ((mobiusSetStabilizer_le M.group (pantsNielsenLiftCarrier M P s)) hf) hne)

/-- Three actual ends, zero through three of them parabolic. No compact-closure
condition is imposed when a cusp is present. -/
def HubbardPantsAlternative {M : HyperbolicSurfaceModel R} {P : Set X}
    {s : M.discCover ⁻¹' P} (W : HubbardCutCompletion M P s) : Prop :=
  ∃ hNE : Geometry.DiscreteGroups.IsNonElementary (pantsNielsenStabilizer M P s),
    ∃ hFG : (pantsNielsenStabilizer M P s).FG, ∃ n b : ℕ,
      n + b = 3 ∧
      HasNielsenFuchsianSignature (hubbardCutDiscGroup M P s) hNE hFG 0 [] n b ∧
      hubbardClosedLiftSphere M P s = Subtype.val ''
        (closure (fuchsianNielsenCore (hubbardCutDiscGroup M P s) hNE) :
          Set (hubbardCutDiscGroup M P s).domain.carrier) ∧
      ∃ e : HubbardCut M P s ≃ₜ threeBoundaryClosedCore (hubbardCutDiscGroup M P s) hNE,
        (∀ w : hubbardClosedLift M P s,
          (e (hubbardCutProjection M P s w)).val =
            mobiusDomainProjection (hubbardCutDiscGroup M P s).domain w.val) ∧
        (∀ a b : HubbardCut M P s, (letI := W.metric; edist a b) =
          hubbardPieceLengthInf (hubbardCutQuotientModel M P s)
            (threeBoundaryClosedCore (hubbardCutDiscGroup M P s) hNE) (e a) (e b)) ∧
        e '' Set.range W.inclusion =
          {v | v.val ∈ threeBoundaryOpenCore (hubbardCutDiscGroup M P s) hNE}

/-- The half of the existing finite annulus which retains its core circle.
After the explicit rescaling w/ρ its radii are exactly [1,ρ). -/
def hubbardHalfAnnulus (ρ : ℝ) : Set (LiZhongQC.annulus 1 (ρ ^ 2)) :=
  {w | ρ ≤ ‖w.val‖}

/-- A finite positive-modulus half-annulus with its actual Poincaré length.
Its full annulus has radii one and ρ² with ρ>1, and its retained core circle
has radius ρ. -/
def HubbardHalfAnnulusAlternative {M : HyperbolicSurfaceModel R} {P : Set X}
    {s : M.discCover ⁻¹' P} (W : HubbardCutCompletion M P s) : Prop :=
  ∃ ρ : ℝ, ∃ hρ : 1 < ρ,
    ∃ Mρ : HyperbolicSurfaceModel
      (roundAnnulusSurface (ρ ^ 2) (one_lt_pow₀ hρ (by decide : (2 : ℕ) ≠ 0))),
      ∃ e : HubbardCut M P s ≃ₜ hubbardHalfAnnulus ρ,
        (∀ a b : HubbardCut M P s, (letI := W.metric; edist a b) =
          hubbardPieceLengthInf Mρ (hubbardHalfAnnulus ρ) (e a) (e b)) ∧
        e '' Set.range W.inclusion = {w | ρ < ‖w.val.val‖}

/-- Closed hyperbolic half-plane; its ideal semicircle is absent. -/
def hubbardClosedHalfDisc : Set Complex.UnitDisc :=
  {w | 0 ≤ (w : ℂ).im}

def hubbardHalfDiscBoundary : Set hubbardClosedHalfDisc :=
  {w | (w.val : ℂ).im = 0}

/-- Keep the actual half-plane isometry as data for the residual-boundary clause. -/
structure HubbardHalfPlaneIdentification {M : HyperbolicSurfaceModel R} {P : Set X}
    {s : M.discCover ⁻¹' P} (W : HubbardCutCompletion M P s) where
  homeomorph : HubbardCut M P s ≃ₜ hubbardClosedHalfDisc
  distance_eq : ∀ a b : HubbardCut M P s, (letI := W.metric; edist a b) =
    discPathEDist (homeomorph a).val (homeomorph b).val
  interior_eq : homeomorph '' Set.range W.inclusion = {w | 0 < (w.val : ℂ).im}

/-- Full three-type decomposition and EVERY limit-geodesic boundary. All
seeds, completion metrics and half-plane maps are chosen once for this Y. -/
def HubbardDecompositionBody (M : HyperbolicSurfaceModel R)
    (Y : Set (EssentialSimpleCircle X)) : Prop :=
  ∃ seeds : (P : HubbardPieceIndex Y) → M.discCover ⁻¹' P.val,
    ∃ completed : (P : HubbardPieceIndex Y) → HubbardCutCompletion M P.val (seeds P),
      ∃ halfPlanes : (P : HubbardPieceIndex Y) →
          Option (HubbardHalfPlaneIdentification (completed P)),
        (∀ P : HubbardPieceIndex Y,
          HubbardPantsAlternative (completed P) ∨
            HubbardHalfAnnulusAlternative (completed P) ∨
              ∃ e : HubbardHalfPlaneIdentification (completed P), halfPlanes P = some e) ∧
        ∀ D ∈ hubbardResidualComponents Y,
          ∃ P : HubbardPieceIndex Y, ∃ e : HubbardHalfPlaneIdentification (completed P),
            halfPlanes P = some e ∧
            ∃ γ : ℝ → UpperHalfPlane,
              IsHGeodesicParam γ ∧ Function.Injective (M.halfPlaneCover ∘ γ) ∧
              Set.range (M.halfPlaneCover ∘ γ) = D ∧
              (completed P).projection ''
                (e.homeomorph.symm '' hubbardHalfDiscBoundary) = D ∧
              ∃ δ : ℝ → hubbardClosedHalfDisc,
                (∀ t u : ℝ, discPathEDist (δ t).val (δ u).val = edist t u) ∧
                Set.range δ = hubbardHalfDiscBoundary ∧
                ∀ t : ℝ, (completed P).projection (e.homeomorph.symm (δ t)) =
                  M.halfPlaneCover (γ t)

/-- Every finite geodesic family extends to a maximal family with intrinsically
complete pieces and all residual-boundary data, on a nonsimplyconnected
hyperbolic surface outside the punctured-disc conformal type. -/
def HubbardFinitePrescribedDecomposition (M : HyperbolicSurfaceModel R) : Prop :=
  ¬ SimplyConnectedSpace X →
    ¬ RiemannConformallyEquivalent R (stableCuspPuncturedDiscRiemannSurface 0) →
    ∀ F : Set (EssentialSimpleCircle X), F.Finite → IsGeodesicMulticurve M F →
      ∃ Y : Set (EssentialSimpleCircle X), F ⊆ Y ∧
        Maximal (IsGeodesicMulticurve M) Y ∧ HubbardDecompositionBody M Y

end LowDimensionalTopology.Unproved.Teichmuller
