module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalBorderedHyperbolicInput
public import LowDimensionalTopology.Unproved.Teichmuller.HubbardDecomposition
public import Mathlib.Topology.MetricSpace.Completion

/-!
# Intrinsically completed pants on the original geodesic-boundary surface

The original metric has its given topology, complete length distance and
geodesic half-plane coordinates compatible with the interior complex atlas.
A cut piece uses its actual intrinsic length and its uniform completion.
All retained boundary circles and both sides of every cut are recorded.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open Set Fuchsian MeasureTheory
open LowDimensionalTopology.Unproved.Teichmuller
open scoped Topology UpperHalfPlane Manifold ContDiff ENNReal unitInterval

/-- The actual complete length metric and compatible geodesic-boundary charts. -/
structure OriginalCompleteGeodesicBoundaryMetric
    {S : Type} [tS : TopologicalSpace S]
    (U : TopologicalSpace.Opens S) (A : RiemannAtlas U) where
  metric : MetricSpace S
  topology_eq : tS = metric.toUniformSpace.toTopologicalSpace
  complete : @CompleteSpace S metric.toUniformSpace
  connected : ConnectedSpace S
  length_distance :
    letI := metric.replaceTopology topology_eq
    ∀ x y : S, edist x y = ⨅ γ : Path x y, eVariationOn γ univ
  charts : Set (OpenPartialHomeomorph S originalBorderedHalfPlane)
  cover : ∀ x : S, ∃ e ∈ charts, x ∈ e.source
  local_isometry :
    letI := metric.replaceTopology topology_eq
    ∀ e ∈ charts, Isometry (fun x : e.source => e x.val)
  interior_iff : ∀ e ∈ charts, ∀ x ∈ e.source,
    x ∈ U ↔ 0 < (e x).val.re
  analytic :
    letI := A.toChartedSpace
    letI := A.isManifold
    ∀ e ∈ charts,
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω
        (fun x : U => ((e x.val).val : ℂ)) {x : U | x.val ∈ e.source}

variable {S : Type} [tS : TopologicalSpace S]
variable {U : TopologicalSpace.Opens S} {A : RiemannAtlas U}

/-- Infimum of all original metric BV lengths of paths inside the same region. -/
def originalRegionLengthInf
    (G : OriginalCompleteGeodesicBoundaryMetric U A)
    (P : Set S) (a b : P) : ℝ≥0∞ :=
  letI := G.metric.replaceTopology G.topology_eq
  ⨅ γ : Path a.val b.val, ⨅ (_hP : ∀ t : unitInterval, γ t ∈ P), eVariationOn γ univ

/-- The intrinsic metric and its canonical completion projection to the original surface. -/
structure OriginalIntrinsicCutCompletion
    (G : OriginalCompleteGeodesicBoundaryMetric U A) (P : Set S) where
  metric : MetricSpace P
  topology_eq : (inferInstance : TopologicalSpace P) = metric.toUniformSpace.toTopologicalSpace
  distance_original :
    letI := metric.replaceTopology topology_eq
    ∀ a b : P, edist a b = originalRegionLengthInf G P a b
  projection :
    letI := metric.replaceTopology topology_eq
    C(UniformSpace.Completion P, S)
  projection_inclusion :
    letI := metric.replaceTopology topology_eq
    ∀ a : P, projection (a : UniformSpace.Completion P) = a.val
  projection_range :
    letI := metric.replaceTopology topology_eq
    Set.range projection = closure P

namespace OriginalIntrinsicCutCompletion

variable {G : OriginalCompleteGeodesicBoundaryMetric U A} {P : Set S}

/-- The actual uniform completion for the same intrinsic metric. -/
abbrev Completed (W : OriginalIntrinsicCutCompletion G P) : Type :=
  @UniformSpace.Completion P (W.metric.replaceTopology W.topology_eq).toUniformSpace

/-- The standard metric of that actual completion. -/
@[instance_reducible] def completedMetric (W : OriginalIntrinsicCutCompletion G P) : MetricSpace W.Completed :=
  letI := W.metric.replaceTopology W.topology_eq
  inferInstance

/-- The canonical inclusion of the original cut component. -/
def inclusion (W : OriginalIntrinsicCutCompletion G P) (a : P) : W.Completed :=
  letI := W.metric.replaceTopology W.topology_eq
  (a : UniformSpace.Completion P)

/-- The same bundled completion projection. -/
def project (W : OriginalIntrinsicCutCompletion G P) : C(W.Completed, S) := W.projection

end OriginalIntrinsicCutCompletion

/-- A simple closed geodesic image, allowing any original circle parameter. -/
def OriginalGeodesicCircleImage
    (G : OriginalCompleteGeodesicBoundaryMetric U A) (c : C(Circle, S)) : Prop :=
  letI := G.metric.replaceTopology G.topology_eq
  ∃ q : C(Circle, S), Function.Injective q ∧ Set.range q = Set.range c ∧
    ∃ ell : ℝ, 0 < ell ∧ ∀ t : ℝ, ∃ eps : ℝ, 0 < eps ∧
      ∀ s ∈ Ioo (t - eps) (t + eps), ∀ u ∈ Ioo (t - eps) (t + eps),
        dist (q (Circle.exp (2 * Real.pi * s))) (q (Circle.exp (2 * Real.pi * u))) =
          ell * |s - u|

/-- A whole proper standard funnel component cut off by one actual geodesic circle. -/
def OriginalHasFunnelEnd (G : OriginalCompleteGeodesicBoundaryMetric U A) : Prop :=
  ∃ c : C(Circle, S), Topology.IsClosedEmbedding c ∧ OriginalGeodesicCircleImage G c ∧
    ∃ x : S, x ∉ Set.range c ∧
      ∃ W : OriginalIntrinsicCutCompletion G (connectedComponentIn (Set.range c)ᶜ x),
        Topology.IsClosedEmbedding W.project ∧
        ∃ rho : ℝ, ∃ hrho : 1 < rho,
          ∃ Mrho : HyperbolicSurfaceModel
            (roundAnnulusSurface (rho ^ 2) (one_lt_pow₀ hrho (by decide : (2 : ℕ) ≠ 0))),
            ∃ e : W.Completed ≃ₜ hubbardHalfAnnulus rho,
              (letI := W.completedMetric
               ∀ a b : W.Completed, edist a b =
                 hubbardPieceLengthInf Mrho (hubbardHalfAnnulus rho) (e a) (e b)) ∧
              e '' Set.range W.inclusion = {w | rho < ‖w.val.val‖} ∧
              W.project '' (Set.range W.inclusion)ᶜ = Set.range c

/-- No whole proper standard funnel end occurs in the original metric. -/
def OriginalHasNoFunnelEnds (G : OriginalCompleteGeodesicBoundaryMetric U A) : Prop :=
  ¬ OriginalHasFunnelEnd G

/-- A genuine genus-zero three-end model with any zero through three cusp ends. -/
structure OriginalGeneralizedPantsModel where
  group : Subgroup Mobius.complexMobiusGroup
  disc : UnitDiscFuchsianGroup group
  non_elementary : DiscreteGroups.IsNonElementary group
  finitely_generated : group.FG
  no_elliptic : ∀ f ∈ group, f ≠ 1 → ¬ Mobius.MobiusElliptic f
  cusps : ℕ
  cuffs : ℕ
  total_ends : cusps + cuffs = 3
  signature : HasNielsenFuchsianSignature disc non_elementary finitely_generated 0 [] cusps cuffs

namespace OriginalGeneralizedPantsModel

/-- The actual closed core in the whole quotient; no ideal cusp points are added. -/
abbrev Core (m : OriginalGeneralizedPantsModel) : Type :=
  ↥(threeBoundaryClosedCore m.disc m.non_elementary)

/-- The strict open core viewed inside the same closed core. -/
def openCore (m : OriginalGeneralizedPantsModel) : Set m.Core :=
  {x | x.val ∈ threeBoundaryOpenCore m.disc m.non_elementary}

/-- The actual Poincare length infimum on the same model core. -/
def lengthInf (m : OriginalGeneralizedPantsModel) (a b : m.Core) : ℝ≥0∞ :=
  hubbardPieceLengthInf (threeBoundaryQuotientModel m.disc m.no_elliptic)
    (threeBoundaryClosedCore m.disc m.non_elementary) a b

end OriginalGeneralizedPantsModel

/-- All actual cuff labels of the selected completed pieces. -/
abbrev OriginalPantsCuffIndex {J : Type} (models : J → OriginalGeneralizedPantsModel) :=
  Σ j : J, Fin (models j).cuffs

/-- A finite family of all actual completed pants, retaining every original and cut boundary. -/
structure OriginalFiniteCompletedPants (G : OriginalCompleteGeodesicBoundaryMetric U A) where
  curves : Set (EssentialSimpleCircle S)
  finite_curves : curves.Finite
  multicurve : IsMulticurve curves
  curves_interior : ∀ c ∈ curves, Set.range c.val ⊆ (U : Set S)
  curves_geodesic : ∀ c ∈ curves, OriginalGeodesicCircleImage G c.val
  finite_pieces : (hubbardPieces curves).Finite
  pieces : (j : HubbardPieceIndex curves) → OriginalIntrinsicCutCompletion G j.val
  models : HubbardPieceIndex curves → OriginalGeneralizedPantsModel
  equivalence : (j : HubbardPieceIndex curves) → (pieces j).Completed ≃ₜ (models j).Core
  distance_eq : ∀ j : HubbardPieceIndex curves,
    letI := (pieces j).completedMetric
    ∀ a b : (pieces j).Completed, edist a b = (models j).lengthInf (equivalence j a) (equivalence j b)
  interior_eq : ∀ j : HubbardPieceIndex curves,
    equivalence j '' ((pieces j).inclusion '' {x : j.val | x.val ∈ U}) = (models j).openCore
  cuffs : (j : HubbardPieceIndex curves) → Fin (models j).cuffs → C(Circle, (pieces j).Completed)
  cuffs_injective : ∀ j : HubbardPieceIndex curves, ∀ k, Function.Injective (cuffs j k)
  cuffs_disjoint : ∀ j : HubbardPieceIndex curves,
    Pairwise (fun k l => Disjoint (Set.range (cuffs j k)) (Set.range (cuffs j l)))
  cuffs_cover : ∀ j : HubbardPieceIndex curves,
    (⋃ k, Set.range (cuffs j k)) = ((pieces j).inclusion '' {x : j.val | x.val ∈ U})ᶜ
  projection_geodesic : ∀ j : HubbardPieceIndex curves, ∀ k,
    Function.Injective ((pieces j).project.comp (cuffs j k)) ∧
      OriginalGeodesicCircleImage G ((pieces j).project.comp (cuffs j k))
  sides : (curves × Fin 2) ↪ OriginalPantsCuffIndex models
  sides_eq : ∀ c : curves, ∀ epsilon : Fin 2,
    let b := sides (c, epsilon)
    Set.range ((pieces b.1).project.comp (cuffs b.1 b.2)) = Set.range c.val.val
  original_boundary_disjoint :
    ((Set.range sides)ᶜ).PairwiseDisjoint
      (fun b : OriginalPantsCuffIndex models =>
        Set.range ((pieces b.1).project.comp (cuffs b.1 b.2)))
  original_boundary_cover :
    (⋃ b : {b : OriginalPantsCuffIndex models // b ∉ Set.range sides},
      Set.range ((pieces b.val.1).project.comp (cuffs b.val.1 b.val.2))) = (U : Set S)ᶜ
  projection_cover : (⋃ j : HubbardPieceIndex curves, Set.range (pieces j).project) = Set.univ

/-- There is a complete finite pants decomposition on the original metric carrier. -/
def HasOriginalFiniteCompletedPants (G : OriginalCompleteGeodesicBoundaryMetric U A) : Prop :=
  Nonempty (OriginalFiniteCompletedPants G)

end LowDimensionalTopology.Geometry.Surfaces
