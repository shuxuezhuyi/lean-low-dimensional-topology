/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordOrdinaryOrbits
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.ElementaryPacking
@[expose] public section
open Set Filter
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

theorem subgroupConjugate_fixed_coordinate (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g : H) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g) • (q.val ξ)=q.val ξ ↔ g • ξ=ξ := by
  change q.val (g.val.val (q.val.symm (q.val ξ)))=q.val ξ ↔ g.val.val ξ=ξ
  rw [q.val.symm_apply_apply]
  exact q.val.injective.eq_iff

theorem subgroupConjugate_point_free (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    ∀k : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,k • q.val ξ=q.val ξ→k=1 := by
  intro k hk
  obtain ⟨g,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
    H).surjective k
  rw [hfree g ((subgroupConjugate_fixed_coordinate H q g ξ).mp hk),map_one]

theorem HasSeparatingMobiusNeighborhood.of_conjugate (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (h : HasSeparatingMobiusNeighborhood
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val ξ)) :
    HasSeparatingMobiusNeighborhood H ξ := by
  obtain ⟨U,hU,hξ,hsep⟩:=h
  refine ⟨q.val ⁻¹' U,hU.preimage (_root_.LowDimensionalTopology.Geometry.Mobius.continuous_mobiusBoundary q),hξ,?_⟩
  intro g hg
  let k:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g
  have hk : k≠1:=by
    intro he
    exact hg ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H).injective (he.trans (map_one _).symm))
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ hz
  apply Set.disjoint_left.mp (hsep k hk) _ hz
  refine ⟨q.val x,hx,?_⟩
  change q.val (g.val.val (q.val.symm (q.val x)))=q.val (g.val.val x)
  rw [q.val.symm_apply_apply]

theorem separatingMobiusNeighborhood_affine_unit (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hi :
      H≤_root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer)
    (hu : ∀f : H,‖(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusMultiplier ⟨f.val,hi f.property⟩ : ℂ)‖=1)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hξ : ξ≠∞) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    HasSeparatingMobiusNeighborhood H ξ := by
  obtain ⟨z,rfl⟩:=OnePoint.ne_infty_iff_exists.mp hξ
  apply separatingMobiusNeighborhood_of_discontinuous H (range (fun z : ℂ=>(z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)))
    OnePoint.isOpenEmbedding_coe.isOpen_range _ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_affine_unit_discontinuous H hd hi hu) _ ⟨z,rfl⟩ hfree
  rintro g _ ⟨w,rfl⟩
  exact ⟨_,(_root_.LowDimensionalTopology.Geometry.Mobius.mobius_affine_formula ⟨g.val,hi g.property⟩ w).symm⟩

theorem separatingMobiusNeighborhood_pair (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hp :
      H≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz : ξ≠((0 : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (hinf : ξ≠∞)
    (hfree : ∀g : H,g • ξ=ξ→g=1) : HasSeparatingMobiusNeighborhood H ξ := by
  obtain ⟨z,rfl⟩:=OnePoint.ne_infty_iff_exists.mp hinf
  have hz0 : z≠0:=fun he=>hz (congrArg ((↑) : ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) he)
  have he : Topology.IsOpenEmbedding (fun z :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.PuncturedPlane=>(z.val :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)):=
    OnePoint.isOpenEmbedding_coe.comp _root_.LowDimensionalTopology.Geometry.DiscreteGroups.puncturedPlaneDomain.isOpen.isOpenEmbedding_subtypeVal
  apply separatingMobiusNeighborhood_of_discontinuous H (range (fun z :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.PuncturedPlane=>(z.val :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)))
    he.isOpen_range _ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_pair_discontinuous H hd
      hp) _ ⟨⟨z,hz0⟩,rfl⟩ hfree
  rintro g _ ⟨w,rfl⟩
  obtain ⟨a,ha|ha⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_zeroInftyPair_normal_form ⟨g.val,hp
    g.property⟩
  · change g.val=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a at ha
    change g.val.val (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_
    rw [ha,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
    exact ⟨⟨(a : ℂ)*w.val,mul_ne_zero a.ne_zero w.property⟩,rfl⟩
  · change g.val=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal at ha
    change g.val.val (w.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_
    rw [ha,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul_reciprocal_coe a w.val w.property]
    exact ⟨⟨(a : ℂ)/w.val,div_ne_zero a.ne_zero w.property⟩,rfl⟩

/-- All discrete elementary groups are genuinely discontinuous near each free sphere point. -/
theorem separatingMobiusNeighborhood_of_elementary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hfree : ∀g : H,g • ξ=ξ→g=1) : HasSeparatingMobiusNeighborhood H ξ := by
  let : DiscreteTopology H:=hd
  by_cases hP : ∃p∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic p
  · obtain ⟨p,hpH,hp⟩:=hP
    obtain ⟨q,hi,hu⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_parabolic_euclidean_coordinates H hd hE p hpH hp
    apply _root_.LowDimensionalTopology.Geometry.Fuchsian.HasSeparatingMobiusNeighborhood.of_conjugate H q ξ
    have hK : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H):=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
    have hξ : q.val ξ≠∞:=by
      intro he
      have hfix : (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H ⟨p,hpH⟩) • q.val ξ=q.val ξ:=by
        rw [he]
        exact hi (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H
          ⟨p,hpH⟩).property
      have hp1:=hfree ⟨p,hpH⟩ ((subgroupConjugate_fixed_coordinate H q ⟨p,hpH⟩ ξ).mp hfix)
      exact hp.1 (congrArg Subtype.val hp1)
    exact separatingMobiusNeighborhood_affine_unit _ hK hi (fun f=>(hu f).1) _ hξ
      (subgroupConjugate_point_free H q ξ hfree)
  by_cases hL : ∃f∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic f
  · obtain ⟨f,hfH,hf⟩:=hL
    obtain ⟨a,b,hab,_hfa,_hfb,hpair⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elementary_loxodromic_fixed_pair H hd hE f hfH hf
    obtain ⟨q,hq⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_invariant_pair_conjugate_zeroInftyPairStabilizer H a b hab hpair
    apply _root_.LowDimensionalTopology.Geometry.Fuchsian.HasSeparatingMobiusNeighborhood.of_conjugate H q ξ
    let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
    let k : K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H ⟨f,hfH⟩
    have hkL : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic k.val:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusLoxodromic_conjugation_forward f q hf
    have hξ : q.val ξ∉({((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞} : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
      intro hξpair
      have horbit : (MulAction.orbit K (q.val ξ)).Finite:=by
        apply (Set.toFinite ({((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)).subset
        rintro _ ⟨g,rfl⟩
        have hpres:=hq g.property
        change g.val.val '' ({((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_ at hpres
        rw [←hpres]
        exact mem_image_of_mem _ hξpair
      have hfix:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.finite_boundary_orbit_fixed_by_loxodromic K k.val k.property hkL (q.val ξ) horbit
      have hf1:=(subgroupConjugate_point_free H q ξ hfree) k hfix
      have hfOrig : (⟨f,hfH⟩ : H)=1:=
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
          H).injective (hf1.trans (map_one _).symm)
      exact hf.1 (congrArg Subtype.val hfOrig)
    exact separatingMobiusNeighborhood_pair K (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H) hq _
      (fun he=>hξ (he ▸ mem_insert _ _)) (fun he=>hξ (he ▸ mem_insert_of_mem _ (mem_singleton _)))
      (subgroupConjugate_point_free H q ξ hfree)
  have hall : ∀f∈H,f≠1→_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f:=by
    intro f hf hn
    rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f hn with hp|hl|he
    · exact False.elim (hP ⟨f,hf,hp⟩)
    · exact False.elim (hL ⟨f,hf,hl⟩)
    · exact he
  obtain ⟨q,hq⟩:=(_root_.LowDimensionalTopology.Geometry.Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint
    H).mp hall
  let : Finite H:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_finite_of_common_H3_fixed H hd q hq
  exact separatingMobiusNeighborhood_of_discontinuous H univ isOpen_univ
    (fun _ _ _=>mem_univ _) (fun _ _ _=>Set.toFinite _) ξ (mem_univ _) hfree

/-- The exact ordinary/free center hypotheses supply a separating neighborhood for every discrete group. -/
theorem separatingMobiusNeighborhood_of_ordinary_all (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hξ :
      ξ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • ξ=ξ→g=1) : HasSeparatingMobiusNeighborhood H ξ := by
  by_cases hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H
  · exact separatingMobiusNeighborhood_of_elementary H hd hE ξ hfree
  · exact separatingMobiusNeighborhood_of_ordinary H hE hd ξ hξ hfree

theorem exists_ford_exterior_of_ordinary_infty_all (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hinf : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) (z : ℍ) :
    ∃B : Matrix.SpecialLinearGroup (Fin
      2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H ∧ z.im≤(B • z).im ∧
      B • z∈mobiusFordCircleExterior H :=
  exists_ford_exterior_of_separating_infty H hd (separatingMobiusNeighborhood_of_ordinary_all H hd ∞ hinf hfree) z

end
end LowDimensionalTopology.Geometry.Fuchsian
