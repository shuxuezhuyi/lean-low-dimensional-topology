module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.ApproximationPolygons
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicSideFiniteness
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonTranslateDiameters
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.ElementaryCyclicClasses
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreApproximation
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreCriterion
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped OnePoint Complex.UnitDisc Pointwise UpperHalfPlane
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

/-- The original closed tiles of any genuine convex locally finite polygon
have only finitely many labels on every sphere-closed set disjoint from the
true limit set. Vanishing Euclidean tile diameters control ordinary ideal
points as well as native compact subsets. -/
theorem IsConvexFuchsianPolygon.closed_tiles_off_limit_finite
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    (K : Set Mobius.ExtendedComplex)
    (hK : IsClosed K)
    (hKL : Disjoint K (fuchsianLimitSet H)) :
    {g : H | ∃z∈fuchsianDomainTile P D g,z.val∈K}.Finite := by
  classical
  by_contra hfin
  let labels : Set H:={g | ∃z∈fuchsianDomainTile P D g,z.val∈K}
  have hInf : labels.Infinite:=hfin
  let e:=hInf.natEmbedding labels
  let g : ℕ→H:=fun n=>(e n).val
  have hg : Function.Injective g:=Subtype.val_injective.comp e.injective
  have hex (n : ℕ) : ∃z∈fuchsianDomainTile P D (g n),z.val∈K := (e n).property
  choose z hz hzK using hex
  obtain ⟨w,hw⟩ := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let seq : ℕ→ℂ × ℂ:=fun n=>((P.finiteCoordinate (g n • w):ℂ),(P.finiteCoordinate (z n):ℂ))
  have hseq (n : ℕ) : seq n∈Metric.closedBall (0:ℂ) 1×ˢMetric.closedBall (0:ℂ) 1 := by
    constructor
    · simpa only [Metric.mem_closedBall,dist_zero_right] using (P.finiteCoordinate (g n • w)).norm_lt_one.le
    · simpa only [Metric.mem_closedBall,dist_zero_right] using (P.finiteCoordinate (z n)).norm_lt_one.le
  obtain ⟨ab,_hab,φ,hφ,hlim⟩ :=
    ((isCompact_closedBall (0:ℂ) 1).prod (isCompact_closedBall (0:ℂ) 1)).tendsto_subseq hseq
  have hp : Tendsto (fun n=>(P.finiteCoordinate (g (φ n) • w):ℂ)) atTop (𝓝 ab.1) :=
    continuous_fst.continuousAt.tendsto.comp hlim
  have hx : Tendsto (fun n=>(P.finiteCoordinate (z (φ n)):ℂ)) atTop (𝓝 ab.2) :=
    continuous_snd.continuousAt.tendsto.comp hlim
  have hcof : Tendsto (g∘φ) atTop cofinite := by
    have hh:=(hg.comp hφ.injective).tendsto_cofinite
    rwa [Nat.cofinite_eq_atTop] at hh
  have hdiam:=hD.euclidean_closed_tile_diam_tendsto.comp hcof
  have hdist : Tendsto (fun n=>dist (P.finiteCoordinate (g (φ n) • w):ℂ)
      (P.finiteCoordinate (z (φ n)):ℂ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _=>dist_nonneg) (fun n=>?_) hdiam
    apply Metric.dist_le_diam_of_mem
    · apply (Metric.isBounded_ball (x:=(0:ℂ)) (r:=1)).subset
      rintro _ ⟨x,_hx,rfl⟩
      exact mem_ball_zero_iff.mpr (P.finiteCoordinate x).norm_lt_one
    · exact ⟨g (φ n) • w,⟨w,subset_closure hw,rfl⟩,rfl⟩
    · exact ⟨z (φ n),hz (φ n),rfl⟩
  have hab : ab.2=ab.1 := (dist_eq_zero.mp (tendsto_nhds_unique (hp.dist hx) hdist)).symm
  have hOrbit : Tendsto (fun n=>g (φ n) • w.val) atTop (𝓝 (ab.1:Mobius.ExtendedComplex)) := by
    convert OnePoint.continuous_coe.continuousAt.tendsto.comp hp using 1
    ext n
    exact (P.finiteCoordinate_extended (g (φ n) • w)).symm
  have hL : (ab.1:Mobius.ExtendedComplex)∈fuchsianLimitSet H := by
    rw [fuchsianLimitSet_eq_nonElementary H hNE]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrbitLimitSet_subset_limitSet H hNE P.discrete w.val
      ⟨g∘φ,hg.comp hφ.injective,hOrbit⟩
  have hxSphere : Tendsto (fun n=>(z (φ n)).val) atTop (𝓝 (ab.2:Mobius.ExtendedComplex)) := by
    convert OnePoint.continuous_coe.continuousAt.tendsto.comp hx using 1
    ext n
    exact (P.finiteCoordinate_extended (z (φ n))).symm
  have hxK : (ab.2:Mobius.ExtendedComplex)∈K :=
    hK.mem_of_tendsto hxSphere (Eventually.of_forall (fun n=>hzK (φ n)))
  rw [hab] at hxK
  exact disjoint_left.mp hKL hxK hL

/-- Every genuine original side label on a closed sphere subset outside the
true limit set belongs to the derived finite closed-tile family. -/
theorem IsConvexFuchsianPolygon.sides_off_limit_finite
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    (K : Set Mobius.ExtendedComplex)
    (hK : IsClosed K)
    (hKL : Disjoint K (fuchsianLimitSet H)) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ ∃z∈S,z.val∈K}.Finite := by
  apply ((_root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.closed_tiles_off_limit_finite hD hNE K hK hKL).image
    (fun g=>closure D∩fuchsianDomainTile P D g)).subset
  rintro S ⟨hS,z,hz,hzK⟩
  obtain ⟨g,_hgn,hEq⟩ := hS.1
  have hzTile : z∈fuchsianDomainTile P D g := (hEq ▸ hz).2
  exact ⟨g,⟨z,hzTile,hzK⟩,hEq.symm⟩

/-- At an actual parabolic ideal point of any original convex locally finite
polygon, a true sphere neighbourhood meets only finitely many original sides.
Its depth comes from the original whole-group horocyclic incidence theorem;
the horizontal width bound supplies a genuine sphere neighbourhood. -/
theorem IsConvexFuchsianPolygon.parabolic_ideal_side_neighborhood
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (ξ : ℂ) (hξ : ξ∈fuchsianPolygonIdealBoundary P D)
    (hfix : f.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex)) :
    ∃ U : Set Mobius.ExtendedComplex,IsOpen U ∧ (ξ:Mobius.ExtendedComplex)∈U ∧
      {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ ∃x∈S,x.val∈U}.Finite := by
  obtain ⟨q,hq,hT,hqξ⟩ := parabolic_unit_halfPlane_normalizer P f hf (ξ:Mobius.ExtendedComplex) hfix
  obtain ⟨A,hA⟩ := halfPlane_chart_real_lift q hq
  obtain ⟨k,_hk,hdeep⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.normalized_parabolic_deep_sides_finite hD ξ hξ q hq A hA hqξ hT
  let ψ:=normalizedPolygonHalfPlaneChart P A
  let S:=ψ '' D
  obtain ⟨w,hw⟩ := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let b:=|(ψ w).re|+1
  have hwidth : ∀z∈S,∀y∈S,y.re<z.re+1 := by
    intro z hz y hy
    exact hD.normalized_horizontal_width ξ hξ q A hA hqξ hT
      ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hz)
      ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hy)
  have hbound : closure S⊆{z : ℍ | |z.re|≤b} := by
    apply closure_minimal
    · intro z hz
      have h₁:=hwidth (ψ w) ⟨w,hw,rfl⟩ z hz
      have h₂:=hwidth z hz (ψ w) ⟨w,hw,rfl⟩
      change |z.re|≤b
      apply abs_le.mpr
      constructor
      · dsimp [b]
        linarith [neg_abs_le (ψ w).re]
      · dsimp [b]
        linarith [le_abs_self (ψ w).re]
    · exact isClosed_le UpperHalfPlane.continuous_re.abs continuous_const
  let B:=Metric.closedBall (0:ℂ) (b+k)
  let L:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).symm '' ((fun z : ℂ=>(z:Mobius.ExtendedComplex)) '' B)
  have hL : IsCompact L := ((isCompact_closedBall (0:ℂ) (b+k)).image
    OnePoint.continuous_coe).image (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).symm.continuous
  have hξL : (ξ:Mobius.ExtendedComplex)∉L := by
    rintro ⟨_,⟨z,_hz,rfl⟩,he⟩
    have hh:=congrArg q.val he
    change q.val (q.val.symm (z:Mobius.ExtendedComplex))=q.val (ξ:Mobius.ExtendedComplex) at hh
    rw [Equiv.apply_symm_apply,hqξ] at hh
    exact OnePoint.coe_ne_infty z hh
  refine ⟨Lᶜ,hL.isClosed.isOpen_compl,hξL,hdeep.subset ?_⟩
  rintro T ⟨hT,x,hx,hxL⟩
  have hxcl : x∈closure D := frontier_subset_closure (hT.subset_frontier hD.locallyFinite.fundamental hx)
  have hxBnd:=hbound (image_closure_subset_closure_image ψ.continuous ⟨x,hxcl,rfl⟩)
  have hxHigh : k<(ψ x).im := by
    by_contra hn
    have hNorm : ((ψ x:ℍ):ℂ)∈B := by
      change dist ((ψ x:ℍ):ℂ) 0≤b+k
      rw [dist_zero_right]
      apply (Complex.norm_le_abs_re_add_abs_im _).trans
      change |(ψ x).re|+|(ψ x).im|≤b+k
      rw [abs_of_pos (ψ x).im_pos]
      exact add_le_add hxBnd (le_of_not_gt hn)
    apply hxL
    refine ⟨((ψ x:ℍ):ℂ),⟨((ψ x:ℍ):ℂ),hNorm,rfl⟩,?_⟩
    apply q.val.injective
    change q.val (q.val.symm _)=q.val x.val
    rw [Equiv.apply_symm_apply]
    exact (halfPlane_chart_coordinate_extended P q A hA x).symm
  exact ⟨hT,ψ x,⟨x,hx,rfl⟩,hxHigh⟩

/-- At every actual ordinary sphere point, a genuine open neighbourhood
meets only finitely many original polygon sides. No extension of native
local finiteness to the ideal boundary is assumed. -/
theorem IsConvexFuchsianPolygon.ordinary_side_neighborhood
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    (p : Mobius.ExtendedComplex)
    (hp : p∉fuchsianLimitSet H) :
    ∃ U : Set Mobius.ExtendedComplex,IsOpen U ∧ p∈U ∧
      {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ ∃x∈S,x.val∈U}.Finite := by
  have hLc : IsClosed (fuchsianLimitSet H) := isClosed_closure
  obtain ⟨K,hKn,hKc,hKsub⟩ := exists_mem_nhds_isClosed_subset (hLc.isOpen_compl.mem_nhds hp)
  obtain ⟨U,hUK,hUo,hpU⟩ := mem_nhds_iff.mp hKn
  have hd : Disjoint K (fuchsianLimitSet H) := disjoint_left.mpr
    (fun x hx hxL=>hKsub hx hxL)
  refine ⟨U,hUo,hpU,(_root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.sides_off_limit_finite hD hNE K hKc hd).subset ?_⟩
  rintro S ⟨hS,x,hx,hxU⟩
  exact ⟨hS,x,hx,hUK hxU⟩

/-- If the actual limit set splits, every original convex locally finite
fundamental polygon has finitely many true sides. The ideal parabolic and
ordinary neighbourhoods are genuinely proved, and compactness is taken in
the unchanged sphere closure of the original polygon. -/
theorem split_limitSet_polygon_sides_finite
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    (hSplit : HasSplitFuchsianLimitSet P)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite := by
  classical
  let C:=closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' D)
  have hLocal (p : C) : ∃U : Set Mobius.ExtendedComplex,IsOpen U ∧ p.val∈U ∧
      {S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ ∃x∈S,x.val∈U}.Finite := by
    by_cases hp : p.val∈fuchsianLimitSet H
    · obtain ⟨ξ,hn,hξ⟩ := fuchsian_limit_unitDisc_finite P p.val hp
      have hξL : (ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H := hξ ▸ hp
      have hξcl : (ξ:Mobius.ExtendedComplex)∈C := hξ ▸ p.property
      have hξE : ξ∈fuchsianPolygonIdealBoundary P D :=
        (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D ξ).mpr ⟨hn,hξcl⟩
      rcases hSplit ξ hξL with ⟨f,hf,hfix⟩|hApprox
      · obtain ⟨U,hUo,hξU,hUf⟩ :=
          _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.parabolic_ideal_side_neighborhood hD f hf ξ hξE hfix
        exact ⟨U,hUo,hξ.symm ▸ hξU,hUf⟩
      · exact False.elim (fuchsian_pointOfApproximation_not_polygon_closure P hD ξ hApprox hξcl)
    · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.ordinary_side_neighborhood hD hNE p.val hp
  choose U hUo hpU hUf using hLocal
  have hC : IsCompact C := isClosed_closure.isCompact
  have hCover : C⊆⋃p : C,U p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hpU ⟨p,hp⟩⟩
  obtain ⟨F,hF⟩ := hC.elim_finite_subcover U hUo hCover
  have hf : (⋃p∈F,{S : Set P.domain.carrier | IsFuchsianPolygonSide P D S ∧ ∃x∈S,x.val∈U p}).Finite :=
    F.finite_toSet.biUnion (fun p _hp=>hUf p)
  apply hf.subset
  intro S hS
  obtain ⟨x,hx⟩ := hS.2.2.nonempty
  have hxC : x.val∈C := image_closure_subset_closure_image continuous_subtype_val
    ⟨x,frontier_subset_closure (hS.subset_frontier hD.locallyFinite.fundamental hx),rfl⟩
  obtain ⟨p,hpF,hxp⟩ := mem_iUnion₂.mp (hF hxC)
  exact mem_iUnion₂.mpr ⟨p,hpF,⟨hS,x,hx,hxp⟩⟩

/-- Every actual elementary Fuchsian group is finitely generated, including
the genuine cyclic and actual conjugate two-generator dihedral cases. -/
theorem elementary_fuchsian_finitelyGenerated
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) : H.FG := by
  classical
  rcases D.elementary_classification hE with hc|⟨u,d,_hdI,_hdR,hgen⟩
  · let := hc
    obtain ⟨r,hr⟩ := exists_zpow_surjective H
    apply (Group.fg_iff_subgroup_fg H).mp
    apply Group.fg_iff.mpr
    refine ⟨{r},?_,finite_singleton r⟩
    apply eq_top_iff.mpr
    intro x _hx
    obtain ⟨n,rfl⟩ := hr x
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (mem_singleton r)) n
  · let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H
    have hK : K.FG := (Subgroup.fg_iff K).mpr
      ⟨{_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d,fuchsianDihedralFlip},hgen.symm,toFinite _⟩
    let := (Group.fg_iff_subgroup_fg K).mpr hK
    let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence u H
    have : Group.FG H:=Group.fg_of_surjective (f:=e.symm.toMonoidHom) e.symm.surjective
    exact (Group.fg_iff_subgroup_fg H).mp this

/--
The reverse implication for the actual original group.
For non-elementary groups the actual arbitrary-polygon finite-side theorem
applies to a genuine free-centre Dirichlet polygon; elementary groups retain
their complete original classification.
-/
theorem split_limitSet_finitelyGenerated {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hSplit : HasSplitFuchsianLimitSet P) : H.FG := by
  classical
  by_cases hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H
  · obtain ⟨w,hw,_hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
    have hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
    have hS:=split_limitSet_polygon_sides_finite P hNE hSplit hD
    exact finite_sided_fuchsianPolygon_finitelyGenerated hD hS.to_subtype
  · exact elementary_fuchsian_finitelyGenerated P.asFuchsianDisc (Classical.not_not.mp hNE)

/--
In its full original elementary and non-elementary
scope, with the actual limit set and original point-of-approximation definition.
-/
theorem fg_iff_limitPoint_parabolic_or_pointOfApproximation
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) : H.FG↔HasSplitFuchsianLimitSet P :=
  ⟨finitelyGenerated_split_limitSet P,split_limitSet_finitelyGenerated P⟩

/--
The remaining universal-polygon implication: every
genuine convex locally finite polygon of the original finitely generated
non-elementary group has finitely many actual sides.
-/
theorem finitelyGenerated_every_convexPolygon_sides_finite
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hFG : H.FG)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    Finite (FuchsianPolygonSides P D) :=
  (split_limitSet_polygon_sides_finite P hNE (finitelyGenerated_split_limitSet P hFG) hD).to_subtype

/--
With all four original statements: finite
generation, finite actual Nielsen-core area in every original convex polygon,
existence of an actual finite-sided convex polygon, and finite sidedness of
every original convex locally finite polygon.
-/
theorem fg_iff_finite_nielsenArea_and_exists_and_all_finite_sided_polygons
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) :
    (H.FG↔∀D : Set P.domain.carrier,IsConvexFuchsianPolygon P D→
      fuchsianNielsenCoreArea P hNE D≠⊤) ∧
    (H.FG↔∃D : Set P.domain.carrier,IsConvexFuchsianPolygon P D ∧
      Finite (FuchsianPolygonSides P D)) ∧
    (H.FG↔∀D : Set P.domain.carrier,IsConvexFuchsianPolygon P D→
      Finite (FuchsianPolygonSides P D)) := by
  obtain ⟨w,hw,_hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  have hD₀:=dirichletDomain_isConvexFuchsianPolygon P w hw
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro hFG D hD
    exact finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
  · intro hArea
    exact finite_nielsenCoreArea_finitelyGenerated P hNE hD₀.locallyFinite.fundamental
      (hArea (dirichletDomain P w) hD₀)
  · intro hFG
    exact ⟨dirichletDomain P w,hD₀,finitelyGenerated_every_convexPolygon_sides_finite P hNE hFG hD₀⟩
  · rintro ⟨D,hD,hFin⟩
    exact finite_sided_fuchsianPolygon_finitelyGenerated hD hFin
  · intro hFG D hD
    exact finitelyGenerated_every_convexPolygon_sides_finite P hNE hFG hD
  · intro hAll
    exact finite_sided_fuchsianPolygon_finitelyGenerated hD₀ (hAll (dirichletDomain P w) hD₀)

end LowDimensionalTopology.Geometry.Fuchsian
