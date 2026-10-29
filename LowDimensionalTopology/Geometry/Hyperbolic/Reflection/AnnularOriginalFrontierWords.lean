module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularAllBoundaryWordLabels
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularOriginalPeripheralGeodesics
public import LowDimensionalTopology.Geometry.Fuchsian.PantsCoreBoundaryComponents
public import Mathlib.Tactic.Choose

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian Surfaces Mobius
variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r) (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => HalfPlaneFuchsianGroup.cayleyData
  (annularPairReflectionHalfPlaneData E r x hE hr hin hout)
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "hFG" => annularPairReflectionDiscGroup_fg E r x hE hr hin hout
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout
local notation "Moriginal" => threeBoundaryQuotientModel P
  (annularPairReflectionDiscGroup_noElliptic E r x hE hr hin hout)

/-- The same three full-period original geodesics label all actual core-frontier components. -/
theorem annularDiscPeripheralWords_all_frontier_components
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (P).asFuchsianDisc (g i))
    (hsig : HasNielsenFuchsianSignature P hNE hFG 0 [] 0 3)
    (A : Fin 3 → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hproj : ∀ i, cayleyMobius * realSLMobius (A i) * cayleyMobius⁻¹ = (g i).val) :
    ∃ q : Fin 3 → OriginalClosedGeodesic Moriginal,
      (∀ i, LiZhongQC.Covers (Moriginal).halfPlaneCover (A i) (q i).toLoop ∧
        Function.Injective ((q i).periodic.lift :
          AddCircle (1 : ℝ) → MobiusDomainQuotient (P).domain) ∧
        (q i).length = ENNReal.ofReal (hTranslationLength (hSLIsometry (A i)))) ∧
      Function.Injective (fun i => range (q i).curve) ∧
      range (fun i => range (q i).curve) =
        {S | ∃ z ∈ frontier (threeBoundaryOpenCore P hNE),
          connectedComponentIn (frontier (threeBoundaryOpenCore P hNE)) z = S} := by
  classical
  have hEach (i : Fin 3) := annularDiscPeripheralWord_original_simple_closed_geodesic
    E r x hE hr hin hout hB i (A i) (hproj i)
  choose hA ht M q hphysical hcov hcircle hlength htrace using hEach
  choose L hL hML using fun i =>
    nielsenBoundaryHyperbolic_axis_mem_family P hNE (g i) (hB i) (M i)
  have hSaved := hsig
  obtain ⟨w, hw, hwN, J, hc, hv, _n, _S, _hr, _hg, _ho, _hp, _hb⟩ := hsig
  let Ew := annularBoundaryWordClassEquiv E r x hE hr hin hout hB hSaved
  let hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin := finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD := dirichletDomain_center_mem P w hw
  let C := NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
  let cyc := nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv
  let Ec := nielsenBoundaryCycleClassesEquiv hD hNE hFG hfin w hwD hwN J hc hv
  let index : Fin 3 ≃ C := Ew.trans Ec.symm
  have hclass (i : Fin 3) : nielsenBoundaryLineCyclicClass P hNE hFG (L i) (hL i) =
      annularBoundaryWordClass E r x hE hr hin hout hB i := by
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    change mobiusSetStabilizer _ ((Subtype.val : (P).domain.carrier → ExtendedComplex) ''
      ((P).finiteCoordinate.symm '' (L i).carrier)) = Subgroup.zpowers (g i).val
    rw [← hML i]
    exact (annularDiscPeripheralWord_axis_stabilizer E r x hE hr hin hout hB i (M i)).2
  have hlabel (i : Fin 3) :
      nielsenBoundaryCycleClassMap hD hNE hFG hfin w hwD hwN J hc hv (index i) =
        nielsenBoundaryLineCyclicClass P hNE hFG (L i) (hL i) :=
    (Ec.apply_symm_apply (Ew i)).trans (hclass i).symm
  have hcoord (z : ℍ) : ((P).finiteCoordinate.symm (halfPlaneToDisc z)).val =
      cayleyMobius.val (halfPlaneBoundaryPoint z) := by
    have he := discFiniteHomeomorph_symm_coe (halfPlaneToDisc z)
    change _ = cayleyMobius.val (((z : ℂ) : ExtendedComplex))
    rw [cayleyMobius_apply, extendedCayley_halfPlane]
    exact he
  have hnative (i : Fin 3) : (P).finiteCoordinate.symm ''
      (halfPlaneToDisc '' (hHyperbolicAxis (A i) (hA i) (ht i)).carrier) =
        (P).finiteCoordinate.symm '' (L i).carrier := by
    apply Subtype.val_injective.image_injective
    rw [← hML i, ← hphysical i]
    simp only [image_image]
    apply image_congr
    intro z _hz
    exact hcoord z
  have hcycle (i : Fin 3) : range (q i).curve = cyc (index i) := by
    rw [htrace i, hnative i]
    obtain ⟨b, hb⟩ := Quotient.exists_rep (index i)
    have hbclass : nielsenBoundaryLineCyclicClass P hNE hFG
        (nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv b).val
        (nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv b).property.1 =
          nielsenBoundaryLineCyclicClass P hNE hFG (L i) (hL i) := by
      change nielsenBoundaryCycleClassMap hD hNE hFG hfin w hwD hwN J hc hv
        (Quotient.mk _ b) = nielsenBoundaryLineCyclicClass P hNE hFG (L i) (hL i)
      exact (congrArg (nielsenBoundaryCycleClassMap hD hNE hFG hfin w hwD hwN J hc hv)
        hb).trans (hlabel i)
    have hp := nielsenBoundaryLine_projection_eq_of_class_eq P hNE hFG _ _ (hL i) _
      hbclass.symm
    have hbcyc := nielsenProjectedBoundaryCycle_eq_completeLine
      hD hNE hFG hfin w hwD hwN J hc hv b
    exact hp.trans (hbcyc.symm.trans (congrArg cyc hb))
  refine ⟨q, fun i => ⟨hcov i, hcircle i, hlength i⟩, ?_, ?_⟩
  · intro i j hij
    apply index.injective
    apply nielsenProjectedBoundaryCycle_injective hD hNE hFG hfin w hwD hwN J hc hv
    exact (hcycle i).symm.trans (hij.trans (hcycle j))
  · rw [threeBoundaryOpenCore_frontierComponents_eq_range hD hNE hFG hfin w hwD hwN J hc hv]
    ext S
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨index i, (hcycle i).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨index.symm c, ?_⟩
      simpa only [index.apply_symm_apply] using hcycle (index.symm c)

end LowDimensionalTopology.Geometry.Hyperbolic

end
