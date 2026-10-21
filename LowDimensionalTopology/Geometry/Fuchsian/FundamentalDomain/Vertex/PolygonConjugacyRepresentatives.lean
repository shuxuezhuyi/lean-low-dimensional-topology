/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.ParabolicPolygonVertices
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Pointwise Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon

/-- A nonidentity original group element cannot fix an interior point of its genuine fundamental domain. -/
theorem IsFuchsianFundamentalDomain.nontrivial_fixed_mem_frontier
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    (f : H) (hf : f ≠ 1) (x : P.domain.carrier) (hfix : f • x = x)
    (hx : x ∈ closure D) : x ∈ frontier D := by
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD).1
  have hxD : x ∉ D := by
    intro hxD
    exact disjoint_left.mp (hD.disjoint_image hf) ⟨x,hxD,hfix⟩ hxD
  simpa only [frontier,hDo.interior_eq,Set.mem_sdiff] using And.intro hx hxD

/-- Every actual elliptic element is conjugate inside the original whole group to one fixing the genuine polygon boundary. -/
theorem IsConvexFuchsianPolygon.elliptic_conjugacy_boundary_representative
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val) :
    ∃ (g : H) (x : P.domain.carrier), x ∈ frontier D ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (g * f * g⁻¹).val ∧ (g * f * g⁻¹) • x = x := by
  obtain ⟨z,hz⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusElliptic_disc_fixed_inside f.val hf (P.image_eq f)
  let a : P.domain.carrier := z
  have hfa : f • a = a := Subtype.ext hz
  obtain ⟨x,hx,hxo⟩ := hD.locallyFinite.fundamental.cycle_nonempty a
  obtain ⟨g,hgx⟩ := MulAction.mem_orbit_iff.mp hxo
  let F : H := g * f * g⁻¹
  have hE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic F.val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_isConj (isConj_iff.mpr ⟨g.val,rfl⟩)).mp hf
  have hfix : F • x = x := by
    rw [← hgx]
    simp only [F,mul_smul,inv_smul_smul,hfa]
  have hne : F ≠ 1 := fun he => hE.1 (congrArg Subtype.val he)
  exact ⟨g,x,hD.locallyFinite.fundamental.nontrivial_fixed_mem_frontier F hne x hfix hx,hE,hfix⟩

/-- Every actual parabolic element is conjugate inside the original whole group to one fixing a genuine proper ideal vertex. -/
theorem IsConvexFuchsianPolygon.parabolic_conjugacy_proper_vertex_representative
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val) :
    ∃ (g : H) (η : Circle), IsProperFuchsianInfiniteVertex P D η ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (g * f * g⁻¹).val ∧
      (g * f * g⁻¹).val.val ((η : ℂ) : OnePoint ℂ) = ((η : ℂ) : OnePoint ℂ) := by
  obtain ⟨ξ,hξ⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.Classification.exists_fixedPoint (_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusEquivFractionalLinear f.val)
  have hfix : f.val.val ξ = ξ := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusEquivFractionalLinear_apply] using hξ
  obtain ⟨g,η,hgη,hη⟩ := hD.locallyFinite.parabolic_fixedPoint_orbit_mem_idealBoundary f hf ξ hfix
  have hηnorm : ‖η‖ = 1 := by
    have hh := hη.2
    simpa only [Metric.mem_sphere,dist_zero_right] using hh
  let v : Circle := ⟨η,mem_sphere_zero_iff_norm.mpr hηnorm⟩
  let F : H := g * f * g⁻¹
  have hpar : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic F.val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨g.val,rfl⟩)).mp hf
  have hFfix : F.val.val ((v : ℂ) : OnePoint ℂ) = ((v : ℂ) : OnePoint ℂ) := by
    rw [← hgη]
    change g.val.val (f.val.val (g.val.val.symm (g.val.val ξ))) = g.val.val ξ
    rw [Equiv.symm_apply_apply,hfix]
  exact ⟨g,v,hD.parabolic_ideal_isProper F hpar v hη hFfix,hpar,hFfix⟩

end LowDimensionalTopology.Geometry.Fuchsian
