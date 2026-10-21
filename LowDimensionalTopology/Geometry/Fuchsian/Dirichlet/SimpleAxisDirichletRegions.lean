module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.CosetRegion
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.AxisTranslateLocalFiniteness
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.AxisDistanceHalfPlanes
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.AffineDiscreteGroups
public import LowDimensionalTopology.Geometry.Mobius.Dynamics.MobiusIteration
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineBisectors
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- In an actual discrete group two hyperbolic axes cannot share exactly one ideal endpoint. -/
theorem discrete_hyperbolic_axes_eq_of_shared_endpoint (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (f g :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ H) (hg : g ∈ H)
    (hgL : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic g) (L M :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hL : L.idealEndpoints = Function.fixedPoints g.val)
    (hM : M.idealEndpoints = Function.fixedPoints f.val)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hpL : p ∈ L.idealEndpoints) (hpM : p ∈ M.idealEndpoints) : L = M := by
  obtain ⟨a,b,_γ,hab,_ha,_hb,hpair,_rest⟩ := L.exists_idealEndpoints_pair
  have hga : g.val a = a := by
    have hh : a ∈ L.idealEndpoints := by rw [hpair];simp
    rw [hL] at hh
    exact hh
  have hgb : g.val b = b := by
    have hh : b ∈ L.idealEndpoints := by rw [hpair];simp
    rw [hL] at hh
    exact hh
  have hfp : f.val p = p := by
    rw [hM] at hpM
    exact hpM
  have hp : p=a ∨ p=b := by simpa only [hpair,mem_insert_iff,mem_singleton_iff] using hpL
  have hfa : f.val a = a := by
    rcases hp with hpa | hpb
    · rw [←hpa];exact hfp
    · have hfbp : f.val b = b := by rw [←hpb];exact hfp
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_shared_loxodromic_endpoints H hH f g hf hg hgL b a hab.symm hgb hga hfbp
  have hfb : f.val b = b := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_shared_loxodromic_endpoints H hH f g hf hg hgL a b hab hga hgb hfa
  have haM : a ∈ M.idealEndpoints := by rw [hM];exact hfa
  have hbM : b ∈ M.idealEndpoints := by rw [hM];exact hfb
  obtain ⟨c,d,_δ,_hcd,_hc,_hd,hpairM,_r⟩ := M.exists_idealEndpoints_pair
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.idealEndpoints_injective
  exact hpair.trans (hpairM.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pair_eq_of_two_mem_ne (hpairM ▸
    haM) (hpairM ▸ hbM) hab)).symm

/-- The true line image of a simple hyperbolic axis is genuinely ultraparallel whenever it differs from the original axis. -/
theorem HalfPlaneFuchsianGroup.simple_axis_translated_line_disjoint {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (g : H) (M :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hM : letI := P.nativeAction; (g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier = M.carrier)
    (hne : M ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).HDisjoint M := by
  let nativeUltraparallelAction := P.nativeAction
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht
  obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  have hBact : (B • · : ℍ → ℍ) '' L.carrier = M.carrier := by
    have he (z : ℍ) : g • z = B • z := P.nativeAction_realSL g B hB z
    simpa only [he] using hM
  have hBpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ B).val.det := by
    change 0 < B.val.det
    rw [B.property]
    norm_num
  have hBg : g.val.val = _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ B)) := by
    rw [←hB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius,MonoidHom.comp_apply,_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_matrix]
  have hends : M.idealEndpoints = Function.fixedPoints (g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*g.val⁻¹).val := by
    rw [L.idealEndpoints_realGL_image M (Matrix.SpecialLinearGroup.mapGL ℝ B) hBpos hBact,
      ←hBg,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_fixedPoints_conjugate _ _).symm
  have hpar : Disjoint L.idealEndpoints M.idealEndpoints := by
    apply Set.disjoint_left.mpr
    intro p hpL hpM
    have heq := discrete_hyperbolic_axes_eq_of_shared_endpoint H P.discrete
      (g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A*g.val⁻¹) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
      (H.mul_mem (H.mul_mem g.property hs.1) (H.inv_mem g.property)) hs.1 hs.2.1.1
      L M (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints A hf ht) hends p hpL hpM
    exact hne heq.symm
  have hcar : Disjoint L.carrier M.carrier := by
    apply P.simple_axis_translates_disjoint A hf ht hs M.carrier ⟨g,hM.symm⟩
    intro he
    exact hne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective he)
  exact ⟨Ne.symm hne,hpar,hcar⟩

/-- The genuine native image line for every original group element. -/
def HalfPlaneFuchsianGroup.nativeLineImage {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (g :
      H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine :=
  Classical.choose ((P.nativeHom g).isometry.halfPlane_image_hLine L)

theorem HalfPlaneFuchsianGroup.nativeLineImage_carrier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (g : H) :
    letI := P.nativeAction
    (g • ·) '' L.carrier = (P.nativeLineImage L g).carrier :=
  Classical.choose_spec ((P.nativeHom g).isometry.halfPlane_image_hLine L)

/-- Every genuine different simple-axis translate gives a regular affine Klein cut for both strict and weak true distances. -/
theorem HalfPlaneFuchsianGroup.simple_axis_cut_exists {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (g : H)
    (hg : letI := P.nativeAction; (g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier ≠ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier) :
    letI := P.nativeAction
    ∃ a : ℂ, ∃ t : ℝ, a ≠ 0 ∧
      (∀ z : ℍ, Metric.infDist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier <
        Metric.infDist z ((g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf
          ht).carrier) ↔ inner ℝ a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < t) ∧
      (∀ z : ℍ, Metric.infDist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier ≤
        Metric.infDist z ((g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier) ↔ inner ℝ a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ t) := by
  let nativeSimpleCutAction := P.nativeAction
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht
  let M := P.nativeLineImage L g
  have himage := P.nativeLineImage_carrier L g
  have hne : M ≠ L := by
    intro he
    apply hg
    exact himage.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier he)
  have hd := P.simple_axis_translated_line_disjoint A hf ht hs g M himage hne
  obtain ⟨w,_u,hw,_hu,_hwu⟩ := L.exists_two_points
  have hwV := P.simple_axis_subset_Voronoi A hf ht hs hw
  have hclose : L.pointDist w < M.pointDist w := by
    change Metric.infDist w L.carrier < Metric.infDist w M.carrier
    rw [←himage]
    exact hwV _ ⟨g,rfl⟩ hg
  obtain ⟨a,t,ha,hlt,hle⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.closer_line_affine_le L M hd w hclose
  refine ⟨a,t,ha,?_,?_⟩
  · intro z
    have hh : Metric.infDist z L.carrier < Metric.infDist z (P.nativeLineImage L
      g).carrier ↔ inner ℝ a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < t := hlt z
    rw [←himage] at hh
    exact hh
  · intro z
    have hh : Metric.infDist z L.carrier ≤ Metric.infDist z (P.nativeLineImage L
      g).carrier ↔ inner ℝ a (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) ≤ t := hle z
    rw [←himage] at hh
    exact hh

/-- The actual infinite axis-cut intersection is the interior of a constructed closed convex Klein region. -/
theorem HalfPlaneFuchsianGroup.simple_axis_affine_region {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    letI := P.nativeAction
    ∃ Q : Set ℂ, IsClosed Q ∧ Convex ℝ Q ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier =
        interior Q ∩ Metric.ball 0 1 ∧
      (∀ z : ℍ, (∀ g : H, Metric.infDist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf
        ht).carrier ≤
        Metric.infDist z ((g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier)) ↔ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z ∈ Q) := by
  let nativeSimpleAffineAction := P.nativeAction
  let S := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
  let J := {g : H | (g • ·) '' S ≠ S}
  have hcut (g : J) := P.simple_axis_cut_exists A hf ht hs g.val g.property
  choose a t ha hlt hle using hcut
  let Q : Set ℂ := {u | ∀ g : J, inner ℝ (a g) u ≤ t g}
  have hQeq : Q = ⋂ g : J, (innerSL ℝ (a g)) ⁻¹' Iic (t g) := by ext u;simp [Q]
  have hQclosed : IsClosed Q := by
    rw [hQeq]
    exact isClosed_iInter (fun g => (isClosed_Iic).preimage (innerSL ℝ (a g)).continuous)
  have hQconv : Convex ℝ Q := by
    rw [hQeq]
    exact convex_iInter (fun g => (convex_Iic _).linear_preimage (innerSL ℝ (a g)).toLinearMap)
  have hstrict (z : ℍ) : z ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) S ↔
      ∀ g : J, inner ℝ (a g) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z) < t g := by
    constructor
    · intro hz g
      exact (hlt g z).mp (hz _ ⟨g.val,rfl⟩ g.property)
    · intro hz T hT hne
      obtain ⟨g,rfl⟩ := hT
      exact (hlt ⟨g,hne⟩ z).mpr (hz ⟨g,hne⟩)
  have hQstrict {u : ℂ} (hu : u ∈ interior Q) (g : J) : inner ℝ (a g) u < t g := by
    let F : StrongDual ℝ ℂ := innerSL ℝ (a g)
    have hF : F ≠ 0 := by
      intro he
      have hv := congrArg (fun B : StrongDual ℝ ℂ => B (a g)) he
      have hp := real_inner_self_pos.mpr (ha g)
      change inner ℝ (a g) (a g) = 0 at hv
      linarith
    have hi : u ∈ interior (F ⁻¹' Iic (t g)) :=
      interior_mono (show Q ⊆ F ⁻¹' Iic (t g) from fun _ hx => hx g) hu
    rw [F.interior_preimage (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nielsen_nonzero_functional_surjective F
      hF),interior_Iic] at hi
    exact hi
  have himage : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) S = interior Q ∩ Metric.ball 0 1 := by
    have hsub : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) S ⊆ Q := by
      rintro u ⟨z,hz,rfl⟩ g
      exact ((hstrict z).mp hz g).le
    have hopen := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isOpenMap _
      (P.hyperbolic_axisVoronoi_isOpen A hs.1 hf ht)
    have hi := interior_maximal hsub hopen
    apply Subset.antisymm
    · rintro u hu
      have hr : u ∈ Set.range _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate := by
        obtain ⟨z,_hz,rfl⟩ := hu
        exact mem_range_self z
      exact ⟨hi hu,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate ▸ hr⟩
    · rintro u ⟨huQ,huB⟩
      obtain ⟨z,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate.symm ▸ huB
      exact ⟨z,(hstrict z).mpr (fun g => hQstrict huQ g),rfl⟩
  refine ⟨Q,hQclosed,hQconv,himage,fun z => ?_⟩
  constructor
  · intro hz g
    exact (hle g z).mp (hz g.val)
  · intro hz g
    by_cases hgn : (g • ·) '' S = S
    · rw [hgn]
    · exact (hle ⟨g,hgn⟩ z).mpr (hz ⟨g,hgn⟩)

/-- The original strict simple-axis region has precisely the literal weak-distance intersection as its closure. -/
theorem HalfPlaneFuchsianGroup.closure_simple_axisVoronoi {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    letI := P.nativeAction
    closure (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier) =
      {z | ∀ g : H, Metric.infDist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
        ≤
        Metric.infDist z ((g • ·) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier)} := by
  let nativeSimpleClosureAction := P.nativeAction
  let S := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
  obtain ⟨Q,hQclosed,hQconv,himage,hweak⟩ := P.simple_axis_affine_region A hf ht hs
  ext z
  constructor
  · intro hz g
    have hc : IsClosed {u : ℍ | Metric.infDist u S ≤ Metric.infDist u ((g • ·) '' S)} :=
      isClosed_le (Metric.continuous_infDist_pt S) (Metric.continuous_infDist_pt _)
    apply closure_minimal (t := {u : ℍ | Metric.infDist u S ≤ Metric.infDist u ((g • ·) '' S)}) _ hc hz
    intro u hu
    by_cases hgn : (g • ·) '' S = S
    · change Metric.infDist u S ≤ Metric.infDist u ((g • ·) '' S)
      rw [hgn]
    · exact (hu _ ⟨g,rfl⟩ hgn).le
  · intro hz
    have hzQ := (hweak z).mp hz
    obtain ⟨w,_u,hw,_hu,_hwu⟩ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf
      ht).exists_two_points
    have hwV := P.simple_axis_subset_Voronoi A hf ht hs hw
    have hInt : (interior Q).Nonempty := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w,
      ((himage ▸ mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate hwV) :
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w ∈ interior Q ∩ Metric.ball 0 1).1⟩
    have hcl : closure (interior Q) = Q :=
      (hQconv.closure_interior_eq_closure_of_nonempty_interior hInt).trans hQclosed.closure_eq
    have hzB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z ∈ Metric.ball (0:ℂ) 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate ▸ mem_range_self z
    have hzI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z ∈ closure (interior Q ∩
      Metric.ball (0:ℂ) 1) :=
      Metric.isOpen_ball.closure_inter ⟨hcl.symm ▸ hzQ,hzB⟩
    rw [←himage] at hzI
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isEmbedding.closure_eq_preimage_closure_image]
    exact hzI

/-- The literal actual simple-axis nearest region is hyperbolically convex. -/
theorem HalfPlaneFuchsianGroup.simple_axisVoronoi_hConvex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier) := by
  let nativeSimpleConvexAction := P.nativeAction
  obtain ⟨Q,_hQclosed,hQconv,himage,_hweak⟩ := P.simple_axis_affine_region A hf ht hs
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mpr
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mpr
  rw [image_image]
  change Convex ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' _)
  rw [himage]
  exact hQconv.interior.inter (convex_ball 0 1)

/-- The true closure of the original simple-axis nearest region meets every orbit of the entire original group. -/
theorem HalfPlaneFuchsianGroup.simple_axisVoronoi_closure_meetsEveryOrbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H ℍ (closure (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier)) := by
  let nativeSimpleCoverAction := P.nativeAction
  let S := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier
  have hdist (g : H) (x : ℍ) (T : Set ℍ) :
      Metric.infDist (g • x) (g • T) = Metric.infDist x T :=
    Metric.infDist_image (P.nativeHom g).isometry
  intro x
  obtain ⟨T,⟨g,hg⟩,hmin⟩ := P.exists_closest_hyperbolic_axis A hs.1 hf ht x
  subst T
  refine ⟨g⁻¹,?_⟩
  rw [P.closure_simple_axisVoronoi A hf ht hs]
  intro h
  change Metric.infDist (g⁻¹ • x) S ≤ Metric.infDist (g⁻¹ • x) (h • S)
  rw [←hdist g (g⁻¹ • x) S,←hdist g (g⁻¹ • x) (h • S),smul_inv_smul]
  exact hmin (g • (h • S)) ⟨g*h,by change g • (h • S) = (g*h) • S;exact (mul_smul _ _ _).symm⟩

/-- The actual nearest-axis region is stable under the entire original native axis stabilizer. -/
theorem HalfPlaneFuchsianGroup.simple_axisVoronoi_coset_stable {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsCosetStableRegion (MulAction.stabilizer H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier)
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier) := by
  let nativeSimpleCosetAction := P.nativeAction
  let nativeSimpleCosetIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion_coset_stable _

/-- No nonempty-region hypothesis is needed for an actual simple hyperbolic axis. -/
theorem HalfPlaneFuchsianGroup.simple_axisVoronoi_nonempty {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val)^2)
    (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    letI := P.nativeAction
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.axisVoronoiRegion (G := H) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf ht).carrier).Nonempty := by
  let nativeSimpleNonemptyAction := P.nativeAction
  obtain ⟨w,_u,hw,_hu,_hwu⟩ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hf
    ht).exists_two_points
  exact ⟨w,P.simple_axis_subset_Voronoi A hf ht hs hw⟩

end LowDimensionalTopology.Geometry.Fuchsian
