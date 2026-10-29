module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularBoundaryClassInjection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairNonElementary
public import LowDimensionalTopology.Geometry.Fuchsian.PantsPrimitiveAxisGeodesic
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicLength

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups Pointwise

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian Surfaces Mobius

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "G" => annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr
local notation "P" =>
  LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.cayleyData
    (annularPairReflectionHalfPlaneData E r x hE hr hin hout)
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "hno" => annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout
local notation "Moriginal" => threeBoundaryQuotientModel P hno

/-- Each literal peripheral word generates the full actual stabilizer of its boundary axis. -/
theorem annularDiscPeripheralWord_axis_stabilizer
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i))
    (i : Fin 3) (M : FuchsianAxisModel (P).asFuchsianDisc (g i).val) :
    MobiusStableSet G M.carrier ∧
      mobiusSetStabilizer G M.carrier = Subgroup.zpowers (g i).val := by
  have hNE := annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
  obtain ⟨⟨a, _ha, hgen⟩, _⟩ := boundaryHyperbolic_axis_quotient_circle hNE (hB i) M
  have hcyc : IsCyclic (mobiusSetStabilizer G M.carrier) := by
    exact ((mobiusSetStabilizer G M.carrier).isCyclic_iff_exists_zpowers_eq_top).mpr
      ⟨a, hgen.symm⟩
  have hg : (g i).val ∈ mobiusSetStabilizer G M.carrier :=
    ⟨(g i).property, M.carrier_invariant⟩
  have hmax := annularDiscPeripheralWord_maximal E r x hE hr hin hout i
  exact ⟨boundaryHyperbolic_axis_stable hNE (hB i) M,
    hmax.2.2 _ (mobiusSetStabilizer_le G M.carrier) hcyc
      (Subgroup.zpowers_le_of_mem hg)⟩

/-- A matrix representing the same literal word supplies its full-period original simple geodesic. -/
theorem annularDiscPeripheralWord_original_simple_closed_geodesic
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i))
    (i : Fin 3) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hproj : cayleyMobius * realSLMobius A * cayleyMobius⁻¹ = (g i).val) :
    ∃ hA : realSLMobius A ≠ 1, ∃ ht : 4 < (Matrix.trace A.val) ^ 2,
      ∃ M : FuchsianAxisModel (P).asFuchsianDisc (g i).val,
      ∃ q : OriginalClosedGeodesic Moriginal,
        cayleyMobius.val ''
          (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hA ht).carrier) = M.carrier ∧
        LiZhongQC.Covers (Moriginal).halfPlaneCover A q.toLoop ∧
        Function.Injective (q.periodic.lift :
          AddCircle (1 : ℝ) → MobiusDomainQuotient (P).domain) ∧
        q.length = ENNReal.ofReal (hTranslationLength (hSLIsometry A)) ∧
        range q.curve = mobiusDomainProjection (P).domain ''
          ((P).finiteCoordinate.symm ''
            (halfPlaneToDisc '' (hHyperbolicAxis A hA ht).carrier)) := by
  let c := cayleyMobius⁻¹
  have hAproj : realSLMobius A = c * (g i).val * c⁻¹ := by
    rw [← hproj]
    dsimp only [c]
    group
  have hAH : MobiusHyperbolic (realSLMobius A) := by
    rw [hAproj]
    exact Mobius.mobiusHyperbolic_conjugation_forward (g i).val c (hB i).hyperbolic
  have hAn := hAH.1.1
  have ht := (realSLMobius_hyperbolic_iff A hAn).mp hAH
  obtain ⟨M⟩ := (P).asFuchsianDisc.axisModel_exists (g i).val (g i).property (hB i).hyperbolic
  have hc : c.val '' (P).asFuchsianDisc.carrier = openHalfPlaneSet := by
    change cayleyMobius.val.symm '' extendedUnitDisc = openHalfPlaneSet
    rw [← cayleyMobius_image_openHalfPlane, cayleyMobius.val.symm_image_image]
  have hchart : c.val '' M.carrier =
      halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier :=
    boundary_axis_carrier_image_in_chart M c hc A hAproj hAn ht
  have hphysical : cayleyMobius.val ''
      (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier) = M.carrier := by
    rw [← hchart]
    change cayleyMobius.val '' (cayleyMobius.val.symm '' M.carrier) = M.carrier
    exact cayleyMobius.val.image_symm_image M.carrier
  obtain ⟨hstable, hgen⟩ :=
    annularDiscPeripheralWord_axis_stabilizer E r x hE hr hin hout hB i M
  have hstablePhysical : MobiusStableSet G (cayleyMobius.val ''
      (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier)) := by
    rw [hphysical]
    exact hstable
  have hgenPhysical : mobiusSetStabilizer G (cayleyMobius.val ''
      (halfPlaneBoundaryPoint '' (hHyperbolicAxis A hAn ht).carrier)) =
        Subgroup.zpowers (cayleyMobius * realSLMobius A * cayleyMobius⁻¹) := by
    rw [hphysical, hproj]
    exact hgen
  obtain ⟨q, hcov, hcircle, htrace⟩ :=
    exists_original_simple_closed_geodesic_of_physical_primitive_axis P hno A hAn ht
      (by rw [hproj]; exact (g i).property) hstablePhysical hgenPhysical
  have hcoord (u : ℍ) : ((P).finiteCoordinate.symm (halfPlaneToDisc u)).val =
      cayleyMobius.val (halfPlaneBoundaryPoint u) := by
    have he := discFiniteHomeomorph_symm_coe (halfPlaneToDisc u)
    change _ = cayleyMobius.val (((u : ℂ) : ExtendedComplex))
    rw [cayleyMobius_apply, extendedCayley_halfPlane]
    exact he
  have hdeck (z : ℍ) : (Moriginal).halfPlaneCover (A • z) =
      (Moriginal).halfPlaneCover z := by
    change mobiusDomainProjection (P).domain ((P).finiteCoordinate.symm
      (halfPlaneToDisc (A • z))) =
        mobiusDomainProjection (P).domain ((P).finiteCoordinate.symm (halfPlaneToDisc z))
    apply Quotient.sound
    refine ⟨g i, Subtype.ext ?_⟩
    change (g i).val.val ((P).finiteCoordinate.symm (halfPlaneToDisc z)).val = _
    rw [hcoord, hcoord, ← hproj]
    change (cayleyMobius * realSLMobius A * cayleyMobius⁻¹) •
      (cayleyMobius • halfPlaneBoundaryPoint z) = cayleyMobius • halfPlaneBoundaryPoint (A • z)
    have hz : halfPlaneBoundaryPoint (A • z) =
        (realSLMobius A) • halfPlaneBoundaryPoint z := (realSLMobius_action A z).symm
    rw [hz]
    simp only [mul_smul, inv_smul_smul]
  let := (threeBoundaryQuotientRiemannSurface P).toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := (Moriginal).exists_halfPlaneCover_uniformization
  have hlength := q.length_eq_translationLength_of_covers hp A ((hΓ A).2 hdeck) ht hcov
  exact ⟨hAn, ht, M, q, hphysical, hcov, hcircle, hlength, htrace⟩

end LowDimensionalTopology.Geometry.Hyperbolic

end
