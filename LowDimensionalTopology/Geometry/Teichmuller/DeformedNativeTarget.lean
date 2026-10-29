module

public import LowDimensionalTopology.Geometry.Teichmuller.DeformedCompactUniformization
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarkingSurjectivity
public import LowDimensionalTopology.Geometry.Teichmuller.BasePointHarmonicTangent
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannStandardModels

/-!
# The actual deformed compact surface as a native harmonic target

The source target and marking are chosen from the existing proved normalized
deformation. Its carrier, topology, complete original complex chart set, covering
projection and exact deformed matrix group are retained. The charted-space
round trip is handled by genuine all-chart analyticity, not equality of chartAt
choices. Native harmonic spaces keep their existing L-infinity subspace norm.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open Surfaces GammaMeasurableBeltrami

universe u

/-- The actual source uniformization remains holomorphic in the inherited
native atlas. Its chosen charts may differ, but their complete chart sets agree. -/
theorem source_uniformization_toNative (Y : LiZhongQC.ClosedRS.{u})
    {Δ : Subgroup Deck} {q : ℍ → Y.carrier} (hq : LiZhongQC.IsUniformization Δ q) :
    let := Y.toNative.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsUniformization Δ q := by
  have hqa : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      Y.toNative.toRiemannAtlas q :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (LiZhongQC.k22u_mdifferentiable_contMDiff hq.2.1)
  let := Y.toNative.toRiemannAtlas.toChartedSpace
  let := Y.toNative.toRiemannAtlas.isManifold
  refine ⟨hq.1, ?_, hq.2.2.1, hq.2.2.2⟩
  have hqa' : RiemannAnalyticMap (RiemannAtlas.ofManifold ℍ)
      (RiemannAtlas.ofManifold Y.carrier) q := by
    rw [RiemannAtlas.ofManifold_toChartedSpace Y.toNative.toRiemannAtlas]
    exact hqa
  exact hqa'.contMDiff_ofManifold.mdifferentiable (by simp)

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (ν : Ball Γ)

/-- The actual compact analytic target from the proved normalized deformation. -/
def deformedTargetSource : LiZhongQC.ClosedRS.{u} :=
  Classical.choose (exists_deformed_uniformization R hgenus hΓ hp ν)

/-- The marking is the same homeomorphism supplied with that source target. -/
def deformedTargetMarking : X ≃ₜ (deformedTargetSource R hgenus hΓ hp ν).carrier :=
  Classical.choose (Classical.choose_spec (exists_deformed_uniformization R hgenus hΓ hp ν))

/-- The exact same compact target, in the pre-existing native surface notation. -/
def deformedNativeSurface :
    ClosedRiemannSurface (deformedTargetSource R hgenus hΓ hp ν).carrier :=
  (deformedTargetSource R hgenus hΓ hp ν).toNative

/-- The original cover transported through the actual marking and normalized
inverse, with no further uniformization choice. -/
def deformedTargetCover : ℍ → (deformedTargetSource R hgenus hΓ hp ν).carrier :=
  fun z => deformedTargetMarking R hgenus hΓ hp ν (p ((normalizedUpperEquiv ν).symm z))

/-- Original source QC marking, exact chosen group, exact chosen cover and
source genus all remain attached to the same actual target. -/
theorem deformedTargetSource_spec :
    let := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsKQCRS (deformedTargetMarking R hgenus hΓ hp ν)
        ((1 + ‖ν.val.val‖) / (1 - ‖ν.val.val‖)) ∧
      LiZhongQC.IsUniformization (deformedGroup hΓ ν) (deformedTargetCover R hgenus hΓ hp ν) ∧
      LiZhongQC.HasGenus (deformedTargetSource R hgenus hΓ hp ν).carrier g :=
  Classical.choose_spec (Classical.choose_spec (exists_deformed_uniformization R hgenus hΓ hp ν))

/-- The entire original source atlas set is retained by the native packing. -/
theorem deformedNativeSurface_atlas :
    (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas =
      RiemannAtlas.ofManifold (deformedTargetSource R hgenus hΓ hp ν).carrier := rfl

/-- Identity in each direction is analytic in the actual original source and
native atlas sets. This asserts compatibility, without comparing chart choices. -/
theorem deformedNativeSurface_atlas_compatible :
    RiemannAnalyticMap
        (RiemannAtlas.ofManifold (deformedTargetSource R hgenus hΓ hp ν).carrier)
        (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas id ∧
      RiemannAnalyticMap (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas
        (RiemannAtlas.ofManifold (deformedTargetSource R hgenus hΓ hp ν).carrier) id :=
  ⟨RiemannAnalyticMap.id _, RiemannAnalyticMap.id _⟩

/-- The same exact deformed group uniformizes the same actual cover in the
native chosen charts, proved by all-chart analytic transport. -/
theorem deformedNativeSurface_uniformization :
    let := (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas.toChartedSpace
    LiZhongQC.IsUniformization (deformedGroup hΓ ν) (deformedTargetCover R hgenus hΓ hp ν) :=
  source_uniformization_toNative (deformedTargetSource R hgenus hΓ hp ν)
    (deformedTargetSource_spec R hgenus hΓ hp ν).2.1

/-- The original actual handle homeomorphism and marking prove the native
target has the same topological genus; no converse from group genus is assumed. -/
theorem deformedNativeSurface_hasGenus :
    (deformedNativeSurface R hgenus hΓ hp ν).HasGenus g := by
  let e : X ≃ₜ CanonicalHandleSurface g := Classical.choice hgenus
  exact ⟨(deformedTargetMarking R hgenus hΓ hp ν).symm.trans e⟩

include R hgenus hp in
/-- The real cover itself proves that the exact deformed group acts freely
up to the unavoidable SL signs. No freeness premise is added. -/
theorem deformedNativeSurface_actsFreely : LiZhongQC.ActsFreely (deformedGroup hΓ ν) := by
  let := (deformedNativeSurface R hgenus hΓ hp ν).toRiemannAtlas.toChartedSpace
  exact LiZhongQC.s27g_actsFreely (deformedNativeSurface_uniformization R hgenus hΓ hp ν)

variable (hg : 1 < g)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- Genuine coordinates on the unchanged harmonic subspace of the actual
native deformed surface, using its original coefficient norm. -/
def deformedHarmonicCoordinates :
    NativePetersson.Harmonic (deformedNativeSurface R hgenus hΓ hp ν) P
      (deformedTargetCover R hgenus hΓ hp ν)
      (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF ≃L[ℂ]
        (Fin (3 * g - 3) → ℂ) :=
  (NativePetersson.harmonicDerivativeEquiv (deformedNativeSurface R hgenus hΓ hp ν) P
    (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) F hF (deformedGroup_spec hΓ ν).1).trans
      (deformedWeightedCoordinates R hg hgenus hΓ hp ν)

/-- At the actual deformed surface's identity marking, the actual native
tangent fibre has its literal harmonic representatives. All group/cover/genus
facts are supplied by the proved deformation rather than new fields. -/
def deformedBaseTangentHarmonicEquiv
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u}) :
    let RY := deformedNativeSurface R hgenus hΓ hp ν
    let hY := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
    let hU := deformedNativeSurface_uniformization R hgenus hΓ hp ν
    let hfree := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
    letI := TeichmullerSpace.canonicalComplexChartedSpace RY hg hY
      (canonicalHandleGroupPresentation g) (deformedGroup_spec hΓ ν).1 hfree hU hsmooth
    TangentSpace 𝓘(ℂ, Fin (3 * g - 3) → ℂ) (TeichmullerSpace.basePoint RY) ≃L[ℂ]
      NativePetersson.Harmonic RY P (deformedTargetCover R hgenus hΓ hp ν) hU F hF :=
  TeichmullerSpace.baseTangentHarmonicEquiv (deformedNativeSurface R hgenus hΓ hp ν) hg
    (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (deformedGroup_spec hΓ ν).1
    (deformedNativeSurface_actsFreely R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hsmooth P F hF

include hg in
/-- The original coefficient projection on the actual deformed surface's
identity tangent has exactly its original harmonic part as representative. -/
theorem deformedBaseTangentHarmonicEquiv_derivative
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})
    (μ : Space (deformedGroup hΓ ν)) :
    let RY := deformedNativeSurface R hgenus hΓ hp ν
    let hY := deformedNativeSurface_hasGenus R hgenus hΓ hp ν
    let hU := deformedNativeSurface_uniformization R hgenus hΓ hp ν
    let hfree := deformedNativeSurface_actsFreely R hgenus hΓ hp ν
    letI := TeichmullerSpace.canonicalComplexChartedSpace RY hg hY
      (canonicalHandleGroupPresentation g) (deformedGroup_spec hΓ ν).1 hfree hU hsmooth
    deformedBaseTangentHarmonicEquiv R hgenus hΓ hp ν hg P F hF hsmooth
        (mfderiv 𝓘(ℂ, Space (deformedGroup hΓ ν)) 𝓘(ℂ, Fin (3 * g - 3) → ℂ)
          (TeichmullerSpace.baseCoefficientProjection RY hg hY
            (deformedGroup_spec hΓ ν).1 hfree hU) 0 μ) =
      (⟨NativePetersson.harmonicProjection RY P
          (deformedTargetCover R hgenus hΓ hp ν) hU F hF μ, ⟨μ, rfl⟩⟩ :
        NativePetersson.Harmonic RY P (deformedTargetCover R hgenus hΓ hp ν) hU F hF) := by
  exact TeichmullerSpace.baseTangentHarmonicEquiv_derivative
    (deformedNativeSurface R hgenus hΓ hp ν) hg
    (deformedNativeSurface_hasGenus R hgenus hΓ hp ν) (deformedGroup_spec hΓ ν).1
    (deformedNativeSurface_actsFreely R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) hsmooth P F hF μ

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
