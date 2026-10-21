module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletParabolicEnds
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.ParabolicPolygonVertices
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonVertexSides
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Topology
open scoped UpperHalfPlane OnePoint Pointwise

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- A bounded connected real set has at most its two true extremal frontier
points. No finite decomposition or regularity assumption is imposed. -/
theorem real_preconnected_bounded_frontier_finite {V : Set ℝ}
    (hp : IsPreconnected V) (hb : BddBelow V) (ha : BddAbove V) :
    (frontier V).Finite := by
  by_cases hn : V.Nonempty
  · apply (Set.toFinite ({sInf V,sSup V} : Set ℝ)).subset
    have hcl : closure V ⊆ Icc (sInf V) (sSup V) :=
      closure_minimal (fun x hx => ⟨csInf_le hb hx,le_csSup ha hx⟩) isClosed_Icc
    intro x hx
    by_cases hxi : x = sInf V
    · simp only [mem_insert_iff,mem_singleton_iff]
      exact Or.inl hxi
    by_cases hxs : x = sSup V
    · simp only [mem_insert_iff,mem_singleton_iff]
      exact Or.inr hxs
    have hxb := hcl (frontier_subset_closure hx)
    obtain ⟨l,hl,hlx⟩ := exists_lt_of_csInf_lt hn (lt_of_le_of_ne hxb.1 (Ne.symm hxi))
    obtain ⟨r,hr,hxr⟩ := exists_lt_of_lt_csSup hn (lt_of_le_of_ne hxb.2 hxs)
    have hsub : Ioo l r ⊆ V := fun _ hy => hp.Icc_subset hl hr ⟨hy.1.le,hy.2.le⟩
    have hxiV : x ∈ interior V :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
        (isOpen_Ioo.mem_nhds ⟨hlx,hxr⟩) hsub)
    exact False.elim (hx.2 hxiV)
  · simp only [Set.not_nonempty_iff_eq_empty.mp hn,frontier_empty,finite_empty]

/-- An actual vertical boundary half-ray of an upward-closed open region has
horizontal coordinate on the true frontier of its horizontal projection. -/
theorem upward_frontier_ray_re_mem_frontier_projection
    {S : Set ℍ} (ho : IsOpen S)
    (hup : ∀ w ∈ S, ∀ Y : ℝ, w.im ≤ Y → ∀ hY : 0 < Y,
      stripVerticalLift w Y hY ∈ S)
    (z : ℍ) (hRay : ∀ Y : ℝ, z.im ≤ Y → ∀ hY : 0 < Y,
      stripVerticalLift z Y hY ∈ frontier S) :
    z.re ∈ frontier (UpperHalfPlane.re '' S) := by
  have hez : stripVerticalLift z z.im z.im_pos = z := by
    apply UpperHalfPlane.ext_re_im <;> rfl
  have hz : z ∈ frontier S := hez ▸ hRay z.im le_rfl z.im_pos
  have hcl : z.re ∈ closure (UpperHalfPlane.re '' S) :=
    mem_closure_image UpperHalfPlane.continuous_re.continuousAt
      (frontier_subset_closure hz)
  have hnot : z.re ∉ UpperHalfPlane.re '' S := by
    rintro ⟨w,hw,hwre⟩
    let Y := max z.im w.im
    have hY : 0 < Y := lt_of_lt_of_le z.im_pos (le_max_left _ _)
    have hwY := hup w hw Y (le_max_right _ _) hY
    have hzY := hRay Y (le_max_left _ _) hY
    have he : stripVerticalLift w Y hY = stripVerticalLift z Y hY := by
      apply UpperHalfPlane.ext_re_im
      · exact hwre
      · rfl
    rw [he] at hwY
    exact hzY.2 (ho.interior_eq.symm ▸ hwY)
  exact ⟨hcl,fun hx => hnot (interior_subset hx)⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance parabolicEndsMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance parabolicEndsBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Every genuine original side meeting a sufficiently deep normalized cusp
contains its actual whole upward half-ray from that point. -/
theorem IsConvexFuchsianPolygon.normalized_deep_side_upward
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (k : ℝ)
    (hInf : (∞ : OnePoint ℂ) ∈ closure
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (normalizedPolygonHalfPlaneChart P A
        '' D)))
    (hgood : ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H →
      (closure (normalizedPolygonHalfPlaneChart P A '' D) ∩
        ((fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion
          k)).Nonempty →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ ∈ closure
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (normalizedPolygonHalfPlaneChart P
          A '' D)))
    {T : Set P.domain.carrier} (hT : IsFuchsianPolygonSide P D T)
    {z : ℍ} (hz : z ∈ normalizedPolygonHalfPlaneChart P A '' T) (hzk : k < z.im)
    (Y : ℝ) (hzY : z.im ≤ Y) (hY : 0 < Y) :
    stripVerticalLift z Y hY ∈ normalizedPolygonHalfPlaneChart P A '' T := by
  let ψ := normalizedPolygonHalfPlaneChart P A
  let S := ψ '' D
  obtain ⟨g,hgn,heT⟩ := hT.1
  have hpres : (q*g.val*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    rw [←hq,_root_.LowDimensionalTopology.Geometry.Surfaces.cusp_conjugate_image,P.image_eq g]
  obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL _ hpres
  have hBN : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨g.val,g.property,hB.symm⟩
  have htile : ψ '' T = closure S ∩ ((fun w : ℍ => B • w) '' closure S) := by
    rw [heT]
    exact normalizedPolygonHalfPlaneChart_closed_tile_inter P D q A hA g B hB
  rw [htile]
  apply cusp_closed_intersection_upward (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
    (ψ.isOpenMap D hD.locallyFinite.fundamental.isOpen)
    ((normalizedPolygonHalfPlaneChart_image P A D).symm ▸ hD.normalized_hConvex A)
    hInf k hgood B hBN (htile ▸ hz) hzk Y hzY hY

/-- Only finitely many true original polygon sides meet a sufficiently deep
horoball at a genuine parabolic ideal endpoint. The depth is derived from the
whole-group horocyclic incidence theorem, not assumed as local finiteness at an
excluded ideal point. -/
theorem IsConvexFuchsianPolygon.normalized_parabolic_deep_sides_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (η : ℂ) (hη : η ∈ fuchsianPolygonIdealBoundary P D)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (hqη : q.val (η : OnePoint ℂ) = ∞)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) :
    ∃ k : ℝ, 1 ≤ k ∧
      {T : Set P.domain.carrier | IsFuchsianPolygonSide P D T ∧
        ((normalizedPolygonHalfPlaneChart P A '' T) ∩ _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k).Nonempty}.Finite := by
  classical
  let ψ := normalizedPolygonHalfPlaneChart P A
  let S := ψ '' D
  let V := UpperHalfPlane.re '' S
  have hSi : S = fordSLNativeHom A '' (P.halfPlaneCoordinate '' D) :=
    normalizedPolygonHalfPlaneChart_image P A D
  have hSo : IsOpen S := ψ.isOpenMap D hD.locallyFinite.fundamental.isOpen
  have hSc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S := hSi.symm ▸ hD.normalized_hConvex A
  have hInf : (∞ : OnePoint ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) := by
    rw [normalizedPolygonHalfPlaneChart_extended_closure P D q A hA]
    exact ⟨(η : OnePoint ℂ),
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D η).mp hη).2,hqη⟩
  have hup : ∀ w ∈ S, ∀ Y : ℝ, w.im ≤ Y → ∀ hY : 0 < Y,
      stripVerticalLift w Y hY ∈ S := open_hConvex_upward_closed hSo hSc hInf
  obtain ⟨k,hk,hgood₀⟩ :=
    hD.locallyFinite.normalized_horocyclic_shrink_to_actual_endpoints q hq A hA hT
  have hgood : ∀ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H →
      (closure S ∩ ((fun z : ℍ => B • z) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion
        k)).Nonempty →
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ∞ ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' S) := by
    simpa only [←hSi] using hgood₀
  have hwidth : ∀ z ∈ S, ∀ w ∈ S, w.re < z.re+1 := by
    intro z hz w hw
    exact hD.normalized_horizontal_width η hη q A hA hqη hT (hSi ▸ hz) (hSi ▸ hw)
  obtain ⟨x,hx⟩ :=
    ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hxS : ψ x ∈ S := ⟨x,hx,rfl⟩
  have hVbelow : BddBelow V := by
    refine ⟨(ψ x).re-1,?_⟩
    rintro y ⟨z,hz,rfl⟩
    linarith [hwidth z hz (ψ x) hxS]
  have hVabove : BddAbove V := by
    refine ⟨(ψ x).re+1,?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact (hwidth (ψ x) hxS z hz).le
  have hDpre :=
    ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.isPreconnected
  have hVpre : IsPreconnected V :=
    (hDpre.image ψ ψ.continuous.continuousOn).image
      UpperHalfPlane.re UpperHalfPlane.continuous_re.continuousOn
  have hVfin : (frontier V).Finite :=
    real_preconnected_bounded_frontier_finite hVpre hVbelow hVabove
  let family : Set (Set P.domain.carrier) := {T | IsFuchsianPolygonSide P D T ∧
    ((ψ '' T) ∩ _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k).Nonempty}
  have hex (T : family) : ∃ z : ℍ, z ∈ ψ '' T.val ∧ k < z.im := T.property.2
  choose z hzT hzk using hex
  have hTray (T : family) (Y : ℝ) (hYz : (z T).im ≤ Y) (hY : 0 < Y) :
      stripVerticalLift (z T) Y hY ∈ ψ '' T.val :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.normalized_deep_side_upward hD q hq A hA k hInf hgood T.property.1
      (hzT T) (hzk T) Y hYz hY
  have hTfr (T : family) (Y : ℝ) (hYz : (z T).im ≤ Y) (hY : 0 < Y) :
      stripVerticalLift (z T) Y hY ∈ frontier S := by
    obtain ⟨v,hv,he⟩ := hTray T Y hYz hY
    rw [←ψ.image_frontier D]
    exact ⟨v,T.property.1.subset_frontier hD.locallyFinite.fundamental hv,he⟩
  let coord : family → frontier V := fun T =>
    ⟨(z T).re,upward_frontier_ray_re_mem_frontier_projection hSo hup (z T) (hTfr T)⟩
  have hcoord : Function.Injective coord := by
    intro T U he
    apply Subtype.ext
    by_contra hTU
    have hdis := hD.distinct_sides_inter_subsingleton T.property.1 U.property.1 hTU
    have hdis' : ((ψ '' T.val) ∩ (ψ '' U.val)).Subsingleton := by
      rw [←image_inter ψ.injective]
      exact hdis.image ψ
    have hre : (z T).re = (z U).re := congrArg Subtype.val he
    let Y := max (z T).im (z U).im
    have hY : 0 < Y := lt_of_lt_of_le (z T).im_pos (le_max_left _ _)
    have heq (Z : ℝ) (hZ : 0 < Z) :
        stripVerticalLift (z T) Z hZ = stripVerticalLift (z U) Z hZ := by
      apply UpperHalfPlane.ext_re_im
      · exact hre
      · rfl
    have hm₁ : stripVerticalLift (z T) Y hY ∈ (ψ '' T.val) ∩ (ψ '' U.val) :=
      ⟨hTray T Y (le_max_left _ _) hY,
        (heq Y hY).symm ▸ hTray U Y (le_max_right _ _) hY⟩
    have hY1 : 0 < Y+1 := by linarith
    have hm₂ : stripVerticalLift (z T) (Y+1) hY1 ∈ (ψ '' T.val) ∩ (ψ '' U.val) :=
      ⟨hTray T (Y+1) (by dsimp [Y]; linarith [le_max_left (z T).im (z U).im]) hY1,
        (heq (Y+1) hY1).symm ▸
          hTray U (Y+1) (by dsimp [Y]; linarith [le_max_right (z T).im (z U).im]) hY1⟩
    have hbad := congrArg UpperHalfPlane.im (hdis' hm₁ hm₂)
    change Y = Y+1 at hbad
    linarith
  let : Finite (frontier V) := hVfin.to_subtype
  let : Finite family := Finite.of_injective coord hcoord
  exact ⟨k,hk,Set.toFinite family⟩

/-- After the actual one-endpoint closure condition is transported by the true
Mobius normalizer, every bounded-width and bounded-height portion lies in an
actual compact subset of the original disc. No compactness at the cusp is
assumed. -/
theorem unitDisc_one_endpoint_low_strip_precompact
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (I : Set P.domain.carrier) (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hI : closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
      I) \
      P.domain.carrier ⊆ {a})
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) (hqa : q.val a = ∞)
    (b k : ℝ) :
    ∃ K : Set P.domain.carrier, IsCompact K ∧
      ∀ x ∈ closure I, |(normalizedPolygonHalfPlaneChart P A x).re| ≤ b →
        (normalizedPolygonHalfPlaneChart P A x).im ≤ k → x ∈ K := by
  let ψ := normalizedPolygonHalfPlaneChart P A
  let B := Metric.closedBall (0:ℂ) (b+k)
  let C : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).symm ''
    ((fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' B)
  let L := closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
    I) ∩ C
  have hCc : IsCompact C := ((isCompact_closedBall (0:ℂ) (b+k)).image
    OnePoint.continuous_coe).image (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
      q).symm.continuous
  have hLc : IsCompact L := hCc.inter_left isClosed_closure
  have haC : a ∉ C := by
    rintro ⟨v,⟨z,hz,rfl⟩,he⟩
    have hh := congrArg q.val he
    change q.val (q.val.symm (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = q.val a at hh
    rw [Equiv.apply_symm_apply,hqa] at hh
    exact (OnePoint.coe_ne_infty z) hh
  have hLrange : L ⊆ range (Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro z hz
    by_cases hzD : z ∈ P.domain.carrier
    · exact ⟨⟨z,hzD⟩,rfl⟩
    · have hza : z = a := mem_singleton_iff.mp (hI ⟨hz.1,hzD⟩)
      exact False.elim (haC (hza ▸ hz.2))
  let K := (Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹' L
  have hKc : IsCompact K :=
    P.domain.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage' hLc hLrange
  refine ⟨K,hKc,?_⟩
  intro x hx hxb hxk
  have hxcl : x.val ∈ closure ((Subtype.val : P.domain.carrier →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' I) :=
    image_closure_subset_closure_image continuous_subtype_val ⟨x,hx,rfl⟩
  have hxB : ((ψ x : ℍ):ℂ) ∈ B := by
    change dist ((ψ x:ℍ):ℂ) 0 ≤ b+k
    rw [dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im _).trans
      (by
        change |(ψ x).re|+|(ψ x).im| ≤ b+k
        rw [abs_of_pos (ψ x).im_pos]
        exact add_le_add hxb hxk)
  refine ⟨hxcl,((ψ x:ℍ):ℂ),⟨((ψ x:ℍ):ℂ),hxB,rfl⟩,?_⟩
  apply q.val.injective
  change q.val (q.val.symm _) = q.val x.val
  rw [Equiv.apply_symm_apply]
  exact (halfPlane_chart_coordinate_extended P q A hA x).symm

/-- In the original whole-group polygon, a genuine one-cusp region meets only
finitely many actual sides in its full closure. Its possible cusp limit is
controlled by the true parabolic normalizer; the remaining low strip is proved
compact and the deep strip is handled without local finiteness at infinity. -/
theorem IsConvexFuchsianPolygon.parabolic_one_end_sides_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D)
    (η : ℂ) (hη : η ∈ fuchsianPolygonIdealBoundary P D)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (hqη : q.val (η : OnePoint ℂ) = ∞)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
    (I : Set P.domain.carrier)
    (hI : closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
      I) \
      P.domain.carrier ⊆ {(η : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}) :
    {T : Set P.domain.carrier | IsFuchsianPolygonSide P D T ∧
      (T ∩ closure I).Nonempty}.Finite := by
  let ψ := normalizedPolygonHalfPlaneChart P A
  let S := ψ '' D
  obtain ⟨k,hk,hdeep⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.normalized_parabolic_deep_sides_finite hD η hη q hq A hA hqη hT
  obtain ⟨x,hx⟩ :=
    ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  let b := |(ψ x).re|+1
  have hwidth : ∀ z ∈ S, ∀ w ∈ S, w.re < z.re+1 := by
    intro z hz w hw
    exact hD.normalized_horizontal_width η hη q A hA hqη hT
      ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hz)
      ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hw)
  have hbound : closure S ⊆ {z : ℍ | |z.re| ≤ b} := by
    apply closure_minimal
    · intro z hz
      have h₁ := hwidth (ψ x) ⟨x,hx,rfl⟩ z hz
      have h₂ := hwidth z hz (ψ x) ⟨x,hx,rfl⟩
      change |z.re| ≤ b
      apply abs_le.mpr
      constructor
      · dsimp [b]
        linarith [neg_abs_le (ψ x).re]
      · dsimp [b]
        linarith [le_abs_self (ψ x).re]
    · exact isClosed_le UpperHalfPlane.continuous_re.abs continuous_const
  obtain ⟨K,hK,hIK⟩ :=
    unitDisc_one_endpoint_low_strip_precompact P I (η :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hI q A hA hqη b k
  apply (hdeep.union (hD.locallyFinite.compact_sides_finite K hK)).subset
  rintro T ⟨hT,z,hzT,hzI⟩
  by_cases hzk : k < (ψ z).im
  · exact Or.inl ⟨hT,ψ z,⟨z,hzT,rfl⟩,hzk⟩
  · have hzclD : z ∈ closure D :=
      frontier_subset_closure (hT.subset_frontier hD.locallyFinite.fundamental hzT)
    have hzclS : ψ z ∈ closure S :=
      image_closure_subset_closure_image ψ.continuous ⟨z,hzclD,rfl⟩
    exact Or.inr ⟨hT,z,hzT,hIK z hzI (hbound hzclS) (le_of_not_gt hzk)⟩

/-- If the sole possible ideal limit of one region is absent from the actual
polygon closure, their true closed intersection is compact in the original
disc. This is a compactness theorem, not an added end hypothesis. -/
theorem unitDisc_one_endpoint_closed_inter_compact
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (D I : Set P.domain.carrier) (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hI : closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
      I) \
      P.domain.carrier ⊆ {a})
    (ha : a ∉ closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      '' D)) :
    IsCompact (closure D ∩ closure I) := by
  let L := closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
    D) ∩
    closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' I)
  have hLc : IsCompact L := (isClosed_closure.inter isClosed_closure).isCompact
  have hLrange : L ⊆ range (Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    intro z hz
    by_cases hzD : z ∈ P.domain.carrier
    · exact ⟨⟨z,hzD⟩,rfl⟩
    · have hza : z = a := mem_singleton_iff.mp (hI ⟨hz.2,hzD⟩)
      exact False.elim (ha (hza ▸ hz.1))
  have hK : IsCompact ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    ⁻¹' L) :=
    P.domain.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage' hLc hLrange
  apply hK.of_isClosed_subset (isClosed_closure.inter isClosed_closure)
  rintro x ⟨hxD,hxI⟩
  exact ⟨image_closure_subset_closure_image continuous_subtype_val ⟨x,hxD,rfl⟩,
    image_closure_subset_closure_image continuous_subtype_val ⟨x,hxI,rfl⟩⟩

/-- A genuine one-endpoint region at any actual parabolic fixed boundary point
meets only finitely many actual polygon sides. Membership of the cusp in the
polygon's ideal closure is decided in the proof, not required as an additional
hypothesis. -/
theorem IsConvexFuchsianPolygon.one_parabolic_limit_sides_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f.val)
    (a : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (ha : a ∈ frontier P.domain.carrier) (hfix :
      f.val.val a = a)
    (I : Set P.domain.carrier)
    (hI : closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
      I) \
      P.domain.carrier ⊆ {a}) :
    {T : Set P.domain.carrier | IsFuchsianPolygonSide P D T ∧
      (T ∩ closure I).Nonempty}.Finite := by
  by_cases haD : a ∈ closure ((Subtype.val : P.domain.carrier →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D)
  · have haC : a ∈ _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle 0 1 := by
      change a ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at ha
      rwa [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle] at ha
    have han : a ≠ ∞ := fun he => _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty 0 1 (he ▸ haC)
    obtain ⟨η,rfl⟩ := OnePoint.ne_infty_iff_exists.mp han
    have hn : ‖η‖ = 1 := by simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero] using haC
    have hη : η ∈ fuchsianPolygonIdealBoundary P D :=
      (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D η).mpr ⟨hn,haD⟩
    obtain ⟨q,hq,hT,hqη⟩ := parabolic_unit_halfPlane_normalizer P f hf (η :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hfix
    obtain ⟨A,hA⟩ := halfPlane_chart_real_lift q hq
    exact _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.parabolic_one_end_sides_finite hD η hη q hq A hA hqη hT I hI
  · have hK := unitDisc_one_endpoint_closed_inter_compact P D I a hI haD
    apply (hD.locallyFinite.compact_sides_finite (closure D ∩ closure I) hK).subset
    rintro T ⟨hT,z,hzT,hzI⟩
    exact ⟨hT,z,hzT,
      frontier_subset_closure (hT.subset_frontier hD.locallyFinite.fundamental hzT),hzI⟩

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- Every actual parabolic developed-curve end of the regular Dirichlet circle
meets only finitely many genuine sides in the entire closed radial end. -/
theorem compactification_parabolic_radial_end_sides_finite
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
    {k : H} {F : ℝ → P.domain.carrier}
    (hArc : d.originalArc hw x ⊆ range F)
    (hF : range F ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : _root_.LowDimensionalTopology.Geometry.Fuchsian.DiscFrontierCurveCompactification P k F) (hpar :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val) :
    {T : Set P.domain.carrier | _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianPolygonSide P
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) T ∧
      (T ∩ closure {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius <
        P.hyperbolicDist w z ∧
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
          d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
          _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x}).Nonempty}.Finite := by
  obtain ⟨a,hfix,ha,I,_hIo,_hIfr,hQI,hIideal⟩ :=
    d.compactification_parabolic_radial_end_region hNE hw x hArc hF hShape hpar
  have hIsides := _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.one_parabolic_limit_sides_finite
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w
      hw) k hpar a ha hfix I hIideal
  apply hIsides.subset
  rintro T ⟨hT,z,hzT,hzQ⟩
  exact ⟨hT,z,hzT,closure_mono hQI hzQ⟩

/-- Every actual regular-circle component either already has a finite family
of true boundary sides on its closed radial end, or supplies a genuine
hyperbolic developed crosscut. Thus the unresolved geometric branch is retained
explicitly rather than hidden in a finite-endedness hypothesis. -/
theorem radial_end_sides_finite_or_hyperbolic_crosscut
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    {T : Set P.domain.carrier | _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianPolygonSide P
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) T ∧
      (T ∩ closure {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius <
        P.hyperbolicDist w z ∧
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
          d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
          _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x}).Nonempty}.Finite ∨
    ∃ k : H, ∃ F : ℝ → P.domain.carrier, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic k.val ∧
      Function.Injective (fun n : ℤ => k^n) ∧ IsProperMap F ∧ IsClosedEmbedding F ∧
      d.originalArc hw x ⊆ range F ∧
      range F ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius) ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.DiscFrontierCurveCompactification P k F := by
  by_cases hzero : d.endpointPeriod hw x = 0
  · obtain ⟨k,F,hk,hproper,hembed,hArc,hF,hShape⟩ :=
      d.aperiodic_compactification_contains_originalArc hw x hzero
    have hOrig := hShape
    rcases hShape with hpar | hhyp
    · exact Or.inl
        (d.compactification_parabolic_radial_end_sides_finite hNE hw x hArc hF hOrig hpar.1)
    · exact Or.inr ⟨k,F,hhyp.1,hk,hproper,hembed,hArc,hF,hOrig⟩
  · exact Or.inl (d.finite_period_radial_end_sides_finite hNE hw x (Nat.pos_of_ne_zero hzero))

end RegularDirichletCircleData
end LowDimensionalTopology.Geometry.Fuchsian
