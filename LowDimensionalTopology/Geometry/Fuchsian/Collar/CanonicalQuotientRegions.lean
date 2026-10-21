/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.HyperbolicCollarSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSeparation
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.ParabolicCusps
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.SimpleClosedCurves
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine canonical region of the unit parabolic is exactly the
literal height-one-half horodisc in the original sphere. -/
theorem canonical_unit_cusp_sphere :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_translation]
  norm_num only [abs_one]
  apply Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact ⟨(z:ℂ),hz,rfl⟩
  · rintro _ ⟨z,hz,rfl⟩
    let w:ℍ:=⟨z,by change 1/2<z.im at hz;linarith only [hz]⟩
    exact ⟨w,hz,rfl⟩

/-- On actual native subsets, the original whole Mobius action is
exactly the actual half-plane action in its sphere coordinate. -/
theorem HalfPlaneFuchsianGroup.native_sphere_image {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (g:H) (S:Set ℍ) :
    letI:=P.nativeAction
    g.val.val '' (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' S)=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' ((fun z:ℍ=>g•z) '' S) := by
  let canonicalQuotientNativeAction:=P.nativeAction
  rw [image_image,image_image]
  exact image_congr (fun z _=>P.nativeAction_boundary g z)

/-- A translate of the true canonical cusp whose original parabolic end
is different is disjoint, with no stable-subset premise supplied. -/
theorem canonical_unit_cusp_disjoint_of_not_fixed {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hT:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (g:H) (hfix:g.val.val ∞≠∞) :
    Disjoint (g.val.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)) := by
  obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  let C:=B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*B⁻¹
  have hT':_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)∈H:=by rwa [realSLMobius_unitTranslation]
  have hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈H:=by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv,hB]
    exact H.mul_mem (H.mul_mem g.property hT') (H.inv_mem g.property)
  have hTp:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)):=by
    rw [realSLMobius_unitTranslation]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr one_ne_zero
  have hCp:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,rfl⟩)).mp hTp
  have hTi:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)).val ∞=∞:=by
    rw [realSLMobius_unitTranslation]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1
  have hCi:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C).val (g.val.val ∞)=g.val.val ∞:=by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv,←hB]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint _ _ ∞ hTi
  have hD:_root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet,_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc,P.preserves⟩
  have hd:=canonical_parabolic_regions_disjoint_fixed_points H hD hE
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) C hT' hC hTp hCp ∞ (g.val.val ∞)
    hTi hCi (Ne.symm hfix)
  have him : g.val.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion C:=by
    rw [←canonical_unit_cusp_sphere,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation,image_image,image_image]
    exact image_congr (fun z _=>by rw [←hB];exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action B z)
  rw [him,←canonical_unit_cusp_sphere]
  exact (Set.disjoint_image_iff
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective).mpr hd.symm

/-- The genuine primitive parabolic canonical region is stable under
the original full elliptic-free group. -/
theorem canonical_unit_cusp_stable {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)) := by
  intro g hg
  by_cases hfix:g.val ∞=∞
  · left
    have hm:g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1):=by
      rw [hp.generates ∞ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)]
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ g).mpr ⟨hg,hfix⟩
    obtain ⟨n,rfl⟩:=hm
    change ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)^n).val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)
    rw [_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslation_zpow]
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_translation (1/2) n
  · right
    exact canonical_unit_cusp_disjoint_of_not_fixed P hE hp.mem ⟨g,hg⟩ hfix

/-- The full true canonical-cusp stabilizer is precisely the primitive
cyclic parabolic subgroup, derived from actual separation and its end. -/
theorem canonical_unit_cusp_stabilizer {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2))=_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup := by
  apply le_antisymm
  · intro g hg
    have hfix:g.val ∞=∞:=by
      by_contra hn
      have hd:=canonical_unit_cusp_disjoint_of_not_fixed P hE hp.mem ⟨g,hg.1⟩ hn
      change Disjoint (g.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere
        (1/2)) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)) at hd
      have he:g.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2):=hg.2
      rw [he] at hd
      exact (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isConnected
        (1/2)).nonempty.ne_empty (disjoint_self.mp hd)
    change g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)
    rw [hp.generates ∞ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ g).mpr ⟨hg.1,hfix⟩
  · intro g hg
    refine ⟨(Subgroup.zpowers_le.mpr hp.mem) hg,?_⟩
    obtain ⟨n,hn⟩:=(_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup_mem g).mp hg
    rw [hn]
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_translation (1/2) n

/-- The actual canonical cusp as a stable subset of the original surface domain. -/
def canonicalCuspSubset {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      1)) : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset P.asFuchsianDisc.domain where
  carrier:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)
  subset_domain:=by
    change _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (1/2)⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨z,by change 1/2<z.im at hz;change 0<z.im;linarith only [hz],rfl⟩
  stable:=canonical_unit_cusp_stable P hE hp

/-- Its original full set stabilizer is the actual primitive cyclic subgroup. -/
theorem canonicalCuspSubset_stabilizer {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    (canonicalCuspSubset P hE hp).stabilizer=_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup :=
  canonical_unit_cusp_stabilizer P hE hp

/-- The actual canonical cusp image is an open subset of the original full quotient. -/
theorem canonicalCuspSubset_image_isOpen {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    IsOpen ((canonicalCuspSubset P hE hp).quotientImage:Set
      (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain)) :=
  (canonicalCuspSubset P hE
    hp).quotientImage_isOpen (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isOpen (1/2))

/-- The stabilizer quotient embeds into the actual original full quotient,
by the canonical original-orbit map, as an open cusp region. -/
theorem canonicalCuspSubset_quotient_isOpenEmbedding {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    Topology.IsOpenEmbedding ((Subtype.val:(canonicalCuspSubset P hE hp).quotientImage→
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain) ∘ (canonicalCuspSubset P hE hp).quotientMap) := by
  let S:=canonicalCuspSubset P hE hp
  have hS:IsOpen (Subtype.val ⁻¹' S.carrier:Set P.asFuchsianDisc.domain.carrier):=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isOpen (1/2)).preimage continuous_subtype_val
  have he:(S.openQuotientHomeomorph hS:S.Quotient→S.quotientImage)=S.quotientMap:=by
    funext x
    exact Quotient.inductionOn x (fun _=>rfl)
  rw [←he]
  exact (canonicalCuspSubset_image_isOpen P hE hp).isOpenEmbedding_subtypeVal.comp
    (S.openQuotientHomeomorph hS).isOpenEmbedding

/-- The actual open cusp image has the genuine exponential punctured-disc
coordinate, with its full quotient topology. -/
def canonicalCuspImageHomeomorph {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    (canonicalCuspSubset P hE
      hp).quotientImage ≃ₜ _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspPuncturedDisc (1/2) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspImageHomeomorph (canonicalCuspSubset P hE hp) (1/2) rfl
    (canonicalCuspSubset_stabilizer P hE hp) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isOpen
      (1/2))
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isConnected (1/2))

/-- The genuine inherited quotient complex atlas makes this actual cusp
coordinate analytic, rather than merely a topological parametrization. -/
theorem canonicalCuspImageHomeomorph_analytic {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (hp:IsPrimitive H (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap ((canonicalCuspSubset P hE
      hp).openImageRiemannSurface P.discontinuous
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isOpen
        (1/2)) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isConnected (1/2))).toRiemannAtlas
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspPuncturedDiscRiemannSurface (1/2)).toRiemannAtlas
      (canonicalCuspImageHomeomorph P hE hp) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspImageHomeomorph_analytic (canonicalCuspSubset P hE
    hp) P.discontinuous (1/2) rfl
    (canonicalCuspSubset_stabilizer P hE hp) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isOpen
      (1/2))
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isConnected (1/2))

/-- The exact normalized canonical cusp radius in the actual exponential
coordinate, encoding the source quantitative size. -/
theorem canonicalCuspRadius : _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspRadius (1/2)=Real.exp (-Real.pi) := by
  unfold _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspRadius
  congr 1
  ring

/-- The actual finite canonical region in the original compactified plane. -/
def nativeCanonicalSphere (A:Matrix.SpecialLinearGroup (Fin 2)
  ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A

/-- The original finite canonical region is equivariant under each real lift. -/
theorem nativeCanonicalSphere_conjugation (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    nativeCanonicalSphere (B*A*B⁻¹)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val '' nativeCanonicalSphere A := by
  rw [nativeCanonicalSphere,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation,nativeCanonicalSphere,image_image,image_image]
  exact image_congr (fun z _=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action B z).symm)

/-- Equal genuine axes and genuine translation lengths give equal true canonical strips. -/
theorem hCanonicalRegion_eq_of_axis_length (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (haxis:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hB.1.1).mp hB))
    (hlen:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B := by
  rw [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic A
    hA).1,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic B hB).1,haxis,hlen]

/-- Equality of the genuine geometric H3 axes gives equality of their
actual native H2 lines, using the proved true geometric embedding. -/
theorem hHyperbolicAxis_eq_of_H3_axis_eq (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) (hB:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (haxis:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA.1.1).mp hA)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hB.1.1).mp hB) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  apply (Set.image_injective.mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis]
  exact haxis

/-- A genuine simple hyperbolic's full canonical strip is stable under
the original full group, obtained from actual axis geometry and the
proved strong collar separation rather than an assumed disjointness. -/
theorem nativeCanonicalSphere_simple_stable {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet H (nativeCanonicalSphere A) := by
  intro g hg
  obtain ⟨B,hB⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hg⟩)
  let C:=B*A*B⁻¹
  have hp:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C=g*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*g⁻¹:=by
    dsimp only [C]
    rw [map_mul,map_mul,map_inv,hB]
  have hK:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate g H=H:=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (H.le_normalizer hg)
  have hsC:IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C):=by
    have hh:=hs.conjugate g
    rwa [hK,←hp] at hh
  have him:g.val '' nativeCanonicalSphere A=nativeCanonicalSphere C:=by
    rw [←hB,←nativeCanonicalSphere_conjugation]
  rw [him]
  rcases (isSimple_iff_conjugate_axes H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A)).mp hs |>.2.2 g hg with he|hd
  · left
    have haxis:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
      rwa [←hp] at he
    unfold nativeCanonicalSphere
    congr 1
    apply hCanonicalRegion_eq_of_axis_length C A hsC.2.1 hs.2.1
    · exact hHyperbolicAxis_eq_of_H3_axis_eq C A hsC.2.1 hs.2.1 haxis
    · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation A B
  · right
    have hn:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)≠_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
      intro heq
      have hd':Disjoint (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusGeodesicAxis (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)):=by rwa [←hp] at hd
      rw [heq] at hd'
      exact hs.axis_nonempty.ne_empty (disjoint_self.mp hd')
    have hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hsC.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hsC.2.1.1.1).mp hsC.2.1)≠
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hs.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hs.2.1.1.1).mp hs.2.1):=by
      intro heq
      apply hn
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis C hsC.2.1.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hsC.2.1.1.1).mp hsC.2.1),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hs.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hs.2.1.1.1).mp hs.2.1),heq]
    have hnd:Disjoint
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hsC.2.1.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff C hsC.2.1.1.1).mp
          hsC.2.1)).carrier
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hs.2.1.1.1 ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hs.2.1.1.1).mp hs.2.1)).carrier:=by
      apply (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective).mp
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis]
      rwa [←hp] at hd
    exact (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective).mpr
      (canonical_simple_hyperbolic_regions_disjoint_of_noncrossing H P.discrete hE C A hsC hs hne hnd)

/-- The true canonical strip of a simple hyperbolic, as a stable subset
of the same original invariant surface domain. -/
def canonicalCollarSubset {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset P.asFuchsianDisc.domain where
  carrier:=nativeCanonicalSphere A
  subset_domain:=by
    rintro _ ⟨z,_hz,rfl⟩
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    exact ⟨(z:ℂ),z.im_pos,rfl⟩
  stable:=nativeCanonicalSphere_simple_stable P hE A hs

/-- These actual canonical strip subsets are open in the original
sphere topology, with the hyperbolic trace condition derived. -/
theorem canonicalCollarSubset_isOpen {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    IsOpen (canonicalCollarSubset P hE A hs).carrier := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.isOpenMap
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_isOpen
  intro ht
  have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hs.2.1.1.1).mp hs.2.1
  rw [ht] at hh
  norm_num at hh

/-- The true canonical strip projects to an open region of the original
full quotient, without identifying distinct stabilizer orbits. -/
theorem canonicalCollarSubset_image_isOpen {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    IsOpen ((canonicalCollarSubset P hE A hs).quotientImage:
      Set (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain)) :=
  (canonicalCollarSubset P hE A hs).quotientImage_isOpen (canonicalCollarSubset_isOpen P hE A hs)

/-- The genuine canonical stabilizer quotient embeds openly into the
original full orbit surface by its actual canonical orbit map. -/
theorem canonicalCollarSubset_quotient_isOpenEmbedding {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    Topology.IsOpenEmbedding ((Subtype.val:(canonicalCollarSubset P hE A hs).quotientImage→
      _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain) ∘ (canonicalCollarSubset P hE A hs).quotientMap) := by
  let S:=canonicalCollarSubset P hE A hs
  have hS:IsOpen (Subtype.val ⁻¹' S.carrier:Set P.asFuchsianDisc.domain.carrier):=
    (canonicalCollarSubset_isOpen P hE A hs).preimage continuous_subtype_val
  have he:(S.openQuotientHomeomorph hS:S.Quotient→S.quotientImage)=S.quotientMap:=by
    funext x
    exact Quotient.inductionOn x (fun _=>rfl)
  rw [←he]
  exact (canonicalCollarSubset_image_isOpen P hE A hs).isOpenEmbedding_subtypeVal.comp
    (S.openQuotientHomeomorph hS).isOpenEmbedding

/-- Membership in the canonical collar is equivalent to the strict hyperbolic
sine bound involving distance to the axis and half the translation length. -/
theorem canonicalCollarSubset_size {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hs:IsSimple H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (z:ℍ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z∈(canonicalCollarSubset P hE A hs).carrier ↔
      Real.sinh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hs.2.1.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hs.2.1.1.1).mp
          hs.2.1)).pointDist z)*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)<1 := by
  change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z∈_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A ↔ _
  have hm:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z∈_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A ↔ z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A:=by
    constructor
    · rintro ⟨w,hw,he⟩
      exact _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective he ▸ hw
    · intro hz
      exact ⟨z,hz,rfl⟩
  rw [hm,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_hyperbolic A hs.2.1).1]
  rfl

end LowDimensionalTopology.Geometry.Fuchsian
