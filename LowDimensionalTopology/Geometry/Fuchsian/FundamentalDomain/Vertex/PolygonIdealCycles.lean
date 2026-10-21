module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonInfiniteVertices
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicDirichletBoundary
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicRayReturns
public import Mathlib.Tactic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Complex.UnitDisc Pointwise OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Local finiteness forbids an injective sequence of actual group translates returning a whole contained ray to one compact set. -/
theorem IsLocallyFiniteFuchsianDomain.no_injective_ray_returns
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (R : Set ℍ)
    (hR : R ⊆ P.halfPlaneCoordinate '' D) (g : ℕ → H) (hg : Function.Injective g)
    (K : Set ℍ) (hK : IsCompact K)
    (hhit : ∀ n, ∃ w ∈ K, P.halfPlaneAction (g n) w ∈ R) : False := by
  let K₀ := P.halfPlaneCoordinate.symm '' K
  have hK₀ : IsCompact K₀ := hK.image P.halfPlaneCoordinate.symm.continuous
  have hf := hD.compact_hits_finite K₀ hK₀
  have hsub : range (fun n => (g n)⁻¹) ⊆
      {a : H | (fuchsianDomainTile P D a ∩ K₀).Nonempty} := by
    rintro a ⟨n,rfl⟩
    obtain ⟨w,hw,hwr⟩ := hhit n
    obtain ⟨y,hy,hey⟩ := hR hwr
    let X := P.halfPlaneCoordinate.symm w
    have hgX : (g n) • X ∈ D := by
      have hcoord : P.halfPlaneCoordinate y = P.halfPlaneCoordinate ((g n) • X) := by
        simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.halfPlaneAction_apply] using hey
      exact P.halfPlaneCoordinate.injective hcoord ▸ hy
    refine ⟨X,?_,w,hw,rfl⟩
    exact ⟨(g n) • X,subset_closure hgX,inv_smul_smul (g n) X⟩
  exact (infinite_range_of_injective (inv_injective.comp hg)) (hf.subset hsub)

/-- An actual ideal-boundary ray contained in the polygon transports to the genuine native half-plane ray. -/
theorem IsConvexFuchsianPolygon.ideal_halfPlane_ray_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (z : P.domain.carrier) (hz : z ∈ D)
    (ξ : ℂ) (hξ : ξ ∈ fuchsianPolygonIdealBoundary P D) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay (P.finiteCoordinate z) (ξ : OnePoint ℂ) ⊆
      P.halfPlaneCoordinate '' D := by
  have hs := image_mono (f := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane) (hD.ideal_canonical_ray_subset z hz ξ hξ)
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' (P.finiteCoordinate '' D) = P.halfPlaneCoordinate '' D := by
    rw [image_image]
    rfl
  exact he ▸ hs

/-- Every original actual element has a genuine real determinant-one lift in the fixed half-plane chart. -/
theorem UnitDiscFuchsianGroup.halfPlaneAction_real_lift
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (g : H) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius ∧
      ∀ z : ℍ, A • z = P.halfPlaneAction g z := by
  have hCi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    have he := congrArg (Set.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val) cayleyMobius_image_openHalfPlane
    have hfun : (fun x : OnePoint ℂ => _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val x)) = id := by
      funext x
      exact inv_smul_smul _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius x
    rw [image_image,hfun,image_id] at he
    exact he.symm
  have hpres : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    calc
      _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val '' (g.val.val '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)) := by
        rw [image_image,image_image]
        rfl
      _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by rw [cayleyMobius_image_openHalfPlane,P.image_eq g,hCi]
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  refine ⟨A,hA,?_⟩
  intro z
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hA]
  exact (P.halfPlaneAction_extended g z).symm

/-- Actual hyperbolic powers return every genuine ray at a specified fixed endpoint to a compact set in the original half-plane chart. -/
theorem UnitDiscFuchsianGroup.hyperbolic_fixed_halfPlane_ray_returns
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (f : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (ξ : OnePoint ℂ)
    (hfix : f.val.val ξ = ξ) :
    ∃ g : H, (g = f ∨ g = f⁻¹) ∧ Function.Injective (fun n : ℕ => g^n) ∧
      ∀ (z : ℍ) (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z), R.idealEndpoint = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ξ →
        ∃ K : Set ℍ, IsCompact K ∧
          ∀ n : ℕ, ∃ w ∈ K, P.halfPlaneAction (g^n) w ∈ R.val := by
  obtain ⟨A,hA,hact⟩ := P.halfPlaneAction_real_lift f
  have hAH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [hA]
    simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ hf
  have hAn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1 := hAH.1.1
  have ht := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAH
  have hξA : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ξ) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ξ := by
    rw [hA]
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (f.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ξ))) = _
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply,hfix]
  obtain ⟨B,hB,hinj,hreturns⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_hyperbolic_fixed_ray_compact_returns A hAn ht
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ξ) hξA
  have heA : fordSLNativeHom A = P.halfPlaneActionHom f := IsometryEquiv.ext hact
  have hg : ∃ g : H, (g = f ∨ g = f⁻¹) ∧ fordSLNativeHom B = P.halfPlaneActionHom g := by
    rcases hB with rfl | rfl
    · exact ⟨f,Or.inl rfl,heA⟩
    · exact ⟨f⁻¹,Or.inr rfl,by rw [map_inv,map_inv,heA]⟩
  obtain ⟨g,hgf,heB⟩ := hg
  have hpow (n : ℕ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B^n) = P.halfPlaneActionHom (g^n) := by
    calc
      _ = fordSLNativeHom (B^n) := rfl
      _ = (fordSLNativeHom B)^n := map_pow _ _ _
      _ = P.halfPlaneActionHom (g^n) := by rw [heB,map_pow]
  refine ⟨g,hgf,?_,?_⟩
  · intro m n he
    apply hinj
    change g^m = g^n at he
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B^m) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B^n)
    rw [hpow,hpow,he]
  · intro z R hR
    obtain ⟨K,hK,hits⟩ := hreturns z R hR
    refine ⟨K,hK,?_⟩
    intro n
    obtain ⟨w,hwR,hwK⟩ := hits n
    refine ⟨w,hwK,?_⟩
    have he := congrArg (fun e : ℍ ≃ᵢ ℍ => e w) (hpow n)
    change B^n • w = P.halfPlaneAction (g^n) w at he
    exact he ▸ hwR

/-- No fixed ideal endpoint of an actual hyperbolic element belongs to the original convex locally finite polygon boundary. -/
theorem IsConvexFuchsianPolygon.hyperbolic_fixed_not_idealBoundary
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (f : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (ξ : ℂ) (hfix : f.val.val (ξ : OnePoint ℂ) = (ξ : OnePoint ℂ)) :
    ξ ∉ fuchsianPolygonIdealBoundary P D := by
  intro hξ
  obtain ⟨z,hz⟩ := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  obtain ⟨g,_hgf,hg,hreturns⟩ := P.hyperbolic_fixed_halfPlane_ray_returns f hf ξ hfix
  have hb : (ξ : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr ((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2
  have hη : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.idealBoundary_cayley_iff _).mpr (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply] using hb)
  have hRay := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHLineRay_discHRay (P.finiteCoordinate z) ξ hb).toHalfPlane
  let R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (P.halfPlaneCoordinate z) :=
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay (P.finiteCoordinate z) ξ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm ξ,hη,hRay⟩
  have hEnd : R.idealEndpoint = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ : OnePoint ℂ) := R.idealEndpoint_unique hRay
  obtain ⟨K,hK,hhit⟩ := hreturns (P.halfPlaneCoordinate z) R hEnd
  exact hD.locallyFinite.no_injective_ray_returns R.val
    (hD.ideal_halfPlane_ray_subset z hz ξ hξ) (fun n => g^n) hg K hK hhit

/-- The fixed-point type assertion in uses actual group elements and the original Euclidean ideal boundary. -/
theorem IsConvexFuchsianPolygon.nonidentity_ideal_fixer_parabolic
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (f : H) (hf : f ≠ 1)
    (ξ : ℂ) (hξ : ξ ∈ fuchsianPolygonIdealBoundary P D)
    (hfix : f.val.val (ξ : OnePoint ℂ) = (ξ : OnePoint ℂ)) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val := by
  have hfn : f.val ≠ 1 := fun he => hf (Subtype.ext he)
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f.val hfn with hp | hl | he
  · exact hp
  · exact False.elim (hD.hyperbolic_fixed_not_idealBoundary f (P.asFuchsianDisc.loxodromic_hyperbolic f hl) ξ hfix hξ)
  · obtain ⟨r,_hr0,hr,hsq⟩ := (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f.val hfn).mp he
    have htrace : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace f.val).re < 4 := by rw [hsq]; exact hr
    exact False.elim (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_disc_trace_lt_four_not_fixed_circle f.val (P.image_eq f) htrace
      ((mem_fuchsianPolygonIdealBoundary P D ξ).mp hξ).2 hfix)

end LowDimensionalTopology.Geometry.Fuchsian
