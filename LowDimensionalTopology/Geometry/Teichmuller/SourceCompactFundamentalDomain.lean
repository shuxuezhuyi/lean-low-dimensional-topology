module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceFuchsianRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.CrossingAxisSourceBounds
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegionIntegral
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S23_QCOnSurfaces

/-!
# Compact integration domains for an original compact uniformizing cover

The original covering supplies a compact whole-orbit cover. The genuine
locally finite Dirichlet construction then has compact relative closure.
Transport back to the original half-plane gives an actual integration domain
for the same matrix group, including its ineffective signs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Fuchsian Hyperbolic Mobius

local instance sourceCompactSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex :=
  borel Mobius.ExtendedComplex
local instance sourceCompactSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- The same original compact cover admits a genuine half-plane fundamental
region whose entire relative closure is compact inside the half-plane. -/
theorem exists_sourceCompactHalfPlaneFundamentalRegion
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) :
    ∃ U : Set ℍ, IsHalfPlaneFundamentalRegion (sourceHalfPlaneFuchsianGroup hΓ) U ∧
      IsCompact (closure U) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  obtain ⟨K, hK, hcoverΓ⟩ := LiZhongQC.utm_exists_compact_translate hp
  let H := Γ.map realSLMobius
  let P := sourceHalfPlaneFuchsianGroup hΓ
  let := P.nativeAction
  have hcover : ∀ z : ℍ, ∃ g : H, g • z ∈ K := by
    intro z
    obtain ⟨A, hA, hAz⟩ := hcoverΓ z
    let g : H := ⟨realSLMobius A, Subgroup.mem_map.mpr ⟨A, hA, rfl⟩⟩
    refine ⟨g, ?_⟩
    rwa [P.nativeAction_realSL g A rfl z]
  let D := P.asFuchsianDisc
  let Q := geometricDiscData D
  let E := geometricDiscHomeomorph D
  let φ := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
    (geometricDiscNormalizer D) H
  let : CompactSpace (MobiusDomainQuotient D.domain) :=
    compactCusps_original_quotient_compact P K hK hcover
  let eQ : MobiusDomainQuotient D.domain ≃ₜ MobiusDomainQuotient Q.domain := by
    apply Homeomorph.Quotient.congr E
    intro x y
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨φ g, (geometricDiscHomeomorph_equivariant D g y).symm.trans (congrArg E hg)⟩
    · rintro ⟨g, hg⟩
      refine ⟨φ.symm g, ?_⟩
      apply E.injective
      change geometricDiscHomeomorph D (φ.symm g • y) = geometricDiscHomeomorph D x
      rw [geometricDiscHomeomorph_equivariant, φ.apply_symm_apply]
      exact hg
  let : CompactSpace (MobiusDomainQuotient Q.domain) := eQ.compactSpace
  obtain ⟨w, hw, _⟩ := exists_actual_dirichlet_horocycle_good_center Q
  let W := dirichletDomain Q w
  have hW := dirichletDomain_locallyFinite Q w hw
  have hCW : IsCompact (closure W) := hW.compact_closure_of_compact_quotient
  let S := E ⁻¹' W
  have hS := geometricModel_fundamentalDomain_of_disc D hW.fundamental
  have hCS : IsCompact (closure S) := by
    change IsCompact (closure (E ⁻¹' W))
    rw [← E.preimage_closure]
    exact E.isCompact_preimage.mpr hCW
  let U := halfPlaneGeometricChart P '' S
  have hU : IsHalfPlaneFundamentalRegion P U :=
    P.isHalfPlaneFundamentalRegion_of_native _
      (halfPlaneGeometricChart_fundamental_image P S hS)
  refine ⟨U, hU, ?_⟩
  change IsCompact (closure (halfPlaneGeometricChart P '' S))
  rw [← (halfPlaneGeometricChart P).image_closure]
  exact hCS.image (halfPlaneGeometricChart P).continuous

/-- The original matrix group has an actual compact planar integration domain
contained in the upper half-plane. No independent domain or boundedness data
are supplied as hypotheses. -/
theorem exists_sourceCompactFundamentalDomainH
    {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p) :
    ∃ F : Set ℂ, LiZhongQC.IsFundamentalDomainH Γ F ∧ IsCompact F := by
  obtain ⟨U, hU, hCU⟩ := exists_sourceCompactHalfPlaneFundamentalRegion R hΓ hp
  refine ⟨closedPlanarRegion U, closedPlanarRegion_isFundamentalDomainH _ hU, ?_⟩
  exact hCU.image UpperHalfPlane.continuous_coe

end LowDimensionalTopology.Geometry.Teichmuller
