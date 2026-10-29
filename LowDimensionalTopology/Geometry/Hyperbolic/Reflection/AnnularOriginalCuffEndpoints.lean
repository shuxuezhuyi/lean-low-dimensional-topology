module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.CommonPerpendicularInvariance
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalFrontierWords
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ThreePeripheralMatrices

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian Mobius Surfaces

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "hFG" => annularPairReflectionDiscGroup_fg E r x hE hr hin hout
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "A" => annularPeripheralMatrix E r x (zero_lt_one.trans hE) hr
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "Moriginal" => threeBoundaryQuotientModel D
  (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)
local notation "π" => HyperbolicSurfaceModel.halfPlaneCover Moriginal

/-- The actual Cayley projection is the unchanged original model's half-plane cover. -/
theorem annularOriginal_halfPlaneCover_eq_cayleyProjection (z : ℍ) :
    π z = mobiusDomainProjection (D).domain ((P).cayleyCoordinate z) := rfl

/-- A given cuff covered by the literal matrix has the image of its given invariant line. -/
theorem annularPeripheralInvariantLine_original_trace
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (i : Fin 3) (q : OriginalClosedGeodesic Moriginal)
    (hcov : LiZhongQC.Covers π (A i) q.toLoop)
    (N : HalfPlaneLine) (hN : (A i • · : ℍ → ℍ) '' N.carrier = N.carrier) :
    range q.curve = π '' N.carrier := by
  obtain ⟨hA, ht, _M, _q, _hp, _hc, _hi, _hl, _hr⟩ :=
    annularDiscPeripheralWord_original_simple_closed_geodesic E r x hE hr hin hout
      hB i (A i) (annularPeripheralMatrix_disc E r x hE hr hin hout i)
  have haxis := hHyperbolicAxis_unique_invariant (A i) hA ht N hN
  have hcoord (z : ℍ) : ((D).finiteCoordinate.symm (halfPlaneToDisc z)).val =
      cayleyMobius.val (halfPlaneBoundaryPoint z) := by
    have he := discFiniteHomeomorph_symm_coe (halfPlaneToDisc z)
    change _ = cayleyMobius.val (((z : ℂ) : ExtendedComplex))
    rw [cayleyMobius_apply, extendedCayley_halfPlane]
    exact he
  have hdeck (z : ℍ) : π (A i • z) = π z := by
    change mobiusDomainProjection (D).domain ((D).finiteCoordinate.symm
      (halfPlaneToDisc (A i • z))) =
        mobiusDomainProjection (D).domain ((D).finiteCoordinate.symm (halfPlaneToDisc z))
    apply Quotient.sound
    refine ⟨g i, Subtype.ext ?_⟩
    change (g i).val.val ((D).finiteCoordinate.symm (halfPlaneToDisc z)).val = _
    rw [hcoord, hcoord, ← annularPeripheralMatrix_disc E r x hE hr hin hout i]
    change (cayleyMobius * realSLMobius (A i) * cayleyMobius⁻¹) •
      (cayleyMobius • halfPlaneBoundaryPoint z) = cayleyMobius • halfPlaneBoundaryPoint (A i • z)
    have hz : halfPlaneBoundaryPoint (A i • z) =
        (realSLMobius (A i)) • halfPlaneBoundaryPoint z :=
      (realSLMobius_action (A i) z).symm
    rw [hz]
    simp only [mul_smul, inv_smul_smul]
  let := (threeBoundaryQuotientRiemannSurface D).toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := (Moriginal).exists_halfPlaneCover_uniformization
  exact (q.trace_eq_axis_image_of_covers hp (A i) ((hΓ (A i)).2 hdeck) hA ht hcov).trans
    (congrArg (fun L : HalfPlaneLine => π '' L.carrier) haxis.symm)

/-- The existing three full-period original simple cuffs contain the exact six feet.
The cuff indices remain the raw peripheral-word order `(01,20,12)`. -/
theorem annularSixFeet_original_cuff_endpoints
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature D hNE hFG 0 [] 0 3)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    ∃ q : Fin 3 → OriginalClosedGeodesic Moriginal,
      (∀ i, LiZhongQC.Covers π (A i) (q i).toLoop ∧
        Function.Injective ((q i).periodic.lift :
          AddCircle (1 : ℝ) → MobiusDomainQuotient (D).domain) ∧
        (q i).length = ENNReal.ofReal (hTranslationLength (hSLIsometry (A i)))) ∧
      Function.Injective (fun i => range (q i).curve) ∧
      range (fun i => range (q i).curve) =
        {T | ∃ z ∈ frontier (threeBoundaryOpenCore D hNE),
          connectedComponentIn (frontier (threeBoundaryOpenCore D hNE)) z = T} ∧
      range (q 0).curve = π '' K12.carrier ∧
      range (q 1).curve = π '' K31.carrier ∧
      range (q 2).curve = π '' K23.carrier ∧
      π p12 ∈ range (q 0).curve ∧ π p21 ∈ range (q 0).curve ∧
      π p13 ∈ range (q 1).curve ∧ π p31 ∈ range (q 1).curve ∧
      π p23 ∈ range (q 2).curve ∧ π p32 ∈ range (q 2).curve := by
  obtain ⟨q, hq, hinj, hall⟩ := annularDiscPeripheralWords_all_frontier_components
    E r x hE hr hin hout hB hsig A (annularPeripheralMatrix_disc E r x hE hr hin hout)
  have ht12 : range (q 0).curve = π '' K12.carrier := by
    apply annularPeripheralInvariantLine_original_trace E r x hE hr hin hout hB 0 (q 0)
      (hq 0).1 K12
    change (reflectionProductSL (S 0) (S 1) • · : ℍ → ℍ) '' K12.carrier = K12.carrier
    exact reflectionProductSL_preserves_perpendicular (S 0) (S 1) K12 p12 p21 h12 h21
  have ht31 : range (q 1).curve = π '' K31.carrier := by
    apply annularPeripheralInvariantLine_original_trace E r x hE hr hin hout hB 1 (q 1)
      (hq 1).1 K31
    change (reflectionProductSL (S 2) (S 0) • · : ℍ → ℍ) '' K31.carrier = K31.carrier
    exact reflectionProductSL_preserves_perpendicular (S 2) (S 0) K31 p31 p13 h31 h13
  have ht23 : range (q 2).curve = π '' K23.carrier := by
    apply annularPeripheralInvariantLine_original_trace E r x hE hr hin hout hB 2 (q 2)
      (hq 2).1 K23
    change (reflectionProductSL (S 1) (S 2) • · : ℍ → ℍ) '' K23.carrier = K23.carrier
    exact reflectionProductSL_preserves_perpendicular (S 1) (S 2) K23 p23 p32 h23 h32
  refine ⟨q, hq, hinj, hall, ht12, ht31, ht23, ?_⟩
  rw [ht12, ht31, ht23]
  exact ⟨⟨p12, h12.2.1, rfl⟩, ⟨p21, h21.2.1, rfl⟩,
    ⟨p13, h13.2.1, rfl⟩, ⟨p31, h31.2.1, rfl⟩,
    ⟨p23, h23.2.1, rfl⟩, ⟨p32, h32.2.1, rfl⟩⟩

/-- Distinct labels in that same actual frontier-component census have disjoint cuff ranges. -/
theorem annularOriginalCuffRanges_pairwise_disjoint
    (q : Fin 3 → OriginalClosedGeodesic Moriginal)
    (hinj : Function.Injective (fun i => range (q i).curve))
    (hall : range (fun i => range (q i).curve) =
      {T | ∃ z ∈ frontier (threeBoundaryOpenCore D hNE),
        connectedComponentIn (frontier (threeBoundaryOpenCore D hNE)) z = T}) :
    Pairwise (fun i j => Disjoint (range (q i).curve) (range (q j).curve)) := by
  intro i j hij
  obtain ⟨u, _hu, hi⟩ := hall.subset (mem_range_self i)
  obtain ⟨v, _hv, hj⟩ := hall.subset (mem_range_self j)
  apply disjoint_left.mpr
  intro z hzi hzj
  apply hij
  apply hinj
  exact hi.symm.trans ((connectedComponentIn_eq (hi.symm ▸ hzi)).trans
    ((connectedComponentIn_eq (hj.symm ▸ hzj)).symm.trans hj))

end LowDimensionalTopology.Geometry.Hyperbolic
