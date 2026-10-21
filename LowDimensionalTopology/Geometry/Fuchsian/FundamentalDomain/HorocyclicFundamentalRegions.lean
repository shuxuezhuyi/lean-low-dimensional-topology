module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicDirichletBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.InvariantFundamentalRegions
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped UpperHalfPlane Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Polygon

/-- A connected set with one bounded-height point cannot first enter a cusp only above a prescribed finite band. -/
theorem connected_halfPlane_hits_height_band {S : Set ℍ} (hS : IsConnected S)
    {w : ℍ} (hw : w ∈ S) {M k : ℝ} (hwM : w.im ≤ M)
    (hhit : (S ∩ {z : ℍ | k < z.im}).Nonempty) :
    ∃ z ∈ S, k < z.im ∧ z.im ≤ max M (k+1) := by
  obtain ⟨v,hvS,hvk⟩ := hhit
  by_cases hvM : v.im ≤ max M (k+1)
  · exact ⟨v,hvS,hvk,hvM⟩
  · have hU : k < max M (k+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    obtain ⟨z,hzS,hz⟩ := hS.isPreconnected.intermediate_value hw hvS
      UpperHalfPlane.continuous_im.continuousOn
      (show max M (k+1) ∈ Icc w.im v.im from
        ⟨hwM.trans (le_max_left _ _),le_of_not_ge hvM⟩)
    exact ⟨z,hzS,hz ▸ hU,hz.le⟩

/-- Actual unit translations, a bounded genuine orbit and local finiteness imply finiteness of cusp images meeting a connected closed domain. -/
theorem native_horocyclic_region_images_finite
    (G : Subgroup (ℍ ≃ᵢ ℍ)) (D : Set ℍ) (hD : IsConnected D) (w : ℍ) (hw : w ∈ D)
    (hfinite : ∀ K : Set ℍ, IsCompact K →
      {g : G | ((g.val : ℍ → ℍ) '' closure D ∩ K).Nonempty}.Finite)
    (hT : ∀ n : ℤ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n : ℝ)) ∈ G)
    (M : ℝ) (hM : ∀ g : G, (g.val w).im ≤ M) (k : ℝ) (hk : 0 < k) :
    {L : Set ℍ | ∃ g : G, L = (g.val : ℍ → ℍ) ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k ∧
      (closure D ∩ L).Nonempty}.Finite := by
  let U := max M (k+1)
  let E : Set ℍ := {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ k ≤ z.im ∧ z.im ≤ U}
  have hE : IsCompact E := halfPlane_rectangle_isCompact _ _ hk
  let F := {g : G | ((g.val : ℍ → ℍ) '' closure D ∩ E).Nonempty}
  have hF : F.Finite := hfinite E hE
  apply (hF.image (fun a : G => ((a⁻¹).val : ℍ → ℍ) ''
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)).subset
  rintro L ⟨g,rfl,x,hxD,z,hzK,hgz⟩
  let S := (g.val.symm : ℍ → ℍ) '' closure D
  have hS : IsConnected S := hD.closure.image _ g.val.symm.continuous.continuousOn
  have hwS : g.val.symm w ∈ S := mem_image_of_mem _ (subset_closure hw)
  have hzS : z ∈ S := ⟨x,hxD,by rw [←hgz,g.val.symm_apply_apply]⟩
  have hM' : (g.val.symm w).im ≤ M := hM g⁻¹
  obtain ⟨v,hvS,hvk,hvU⟩ := connected_halfPlane_hits_height_band hS hwS hM' ⟨z,hzS,hzK⟩
  obtain ⟨n,hn0,hn1,hnim⟩ := translation_into_closed_unit_strip v
  let t : G := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n : ℝ)),hT n⟩
  have htim (z : ℍ) : (t.val z).im = z.im := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im _ _
  have htiim (z : ℍ) : ((t⁻¹).val z).im = z.im := by
    have he := htim (t.val.symm z)
    rw [t.val.apply_symm_apply] at he
    exact he.symm
  let a := t*g⁻¹
  have haF : a ∈ F := by
    obtain ⟨u,hu,hgu⟩ := hvS
    refine ⟨t.val v,⟨u,hu,?_⟩,?_⟩
    · change t.val (g.val.symm u) = t.val v
      rw [hgu]
    · exact ⟨hn0,hn1,by rw [htim]; exact hvk.le,by rw [htim]; exact hvU⟩
  have hpres : ((t⁻¹).val : ℍ → ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k = _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      change k < ((t⁻¹).val y).im
      rw [htiim]
      exact hy
    · intro hz
      refine ⟨t.val z,?_,t.val.symm_apply_apply z⟩
      change k < (t.val z).im
      rw [htim]
      exact hz
  refine ⟨a,haF,?_⟩
  have he : a⁻¹ = g*t⁻¹ := by dsimp only [a]; group
  change ((a⁻¹).val : ℍ → ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k =
    (g.val : ℍ → ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k
  rw [he]
  change ((fun z : ℍ => g.val ((t⁻¹).val z)) ''
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) = _
  rw [←image_image,hpres]

/-- The actual compact-hit finiteness survives the genuine whole-group half-plane chart and any native isometric conjugation. -/
theorem IsLocallyFiniteFuchsianDomain.native_conjugate_compact_hits_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (F : ℍ ≃ᵢ ℍ) (K : Set ℍ) (hK : IsCompact K) :
    {e : nativeConjugateGroup F P.halfPlaneActionHom.range |
      ((e.val : ℍ → ℍ) '' closure (F '' (P.halfPlaneCoordinate '' D)) ∩ K).Nonempty}.Finite := by
  let ψ : P.domain.carrier ≃ₜ ℍ := P.halfPlaneCoordinate.trans F.toHomeomorph
  let G := nativeConjugateGroup F P.halfPlaneActionHom.range
  let E : H → G := fun g => ⟨MulAut.conj F (P.halfPlaneAction g),
    ⟨P.halfPlaneAction g,⟨g,rfl⟩,rfl⟩⟩
  have haction (g : H) (u : P.domain.carrier) : (E g).val (ψ u) = ψ (g • u) := by
    change F (P.halfPlaneAction g (F.symm (F (P.halfPlaneCoordinate u)))) =
      F (P.halfPlaneCoordinate (g • u))
    rw [F.symm_apply_apply,P.halfPlaneAction_coordinate]
  have hf := hD.compact_hits_finite (ψ.symm '' K) (hK.image ψ.symm.continuous)
  apply (hf.image E).subset
  rintro e ⟨y,⟨x,hx,hex⟩,hyK⟩
  obtain ⟨f,⟨g,hg⟩,hfe⟩ := e.property
  have hee : E g = e := by
    apply Subtype.ext
    exact (congrArg (MulAut.conj F) hg).trans hfe
  have hxψ : x ∈ closure (ψ '' D) := by
    have hs : ψ '' D = F '' (P.halfPlaneCoordinate '' D) := by rw [image_image]; rfl
    rw [hs]
    exact hx
  obtain ⟨u,hu,hux⟩ := (ψ.image_closure D).symm ▸ hxψ
  rw [←hee,←hux,haction] at hex
  refine ⟨g,⟨g • u,⟨u,hu,rfl⟩,y,hyK,?_⟩,hee⟩
  rw [←hex,ψ.symm_apply_apply]

/-- The actual discrete whole-group native image has a uniform genuine orbit-height bound when it contains the unit translation. -/
theorem fordNativeGroup_orbit_height_bound (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ H) (w : ℍ)
    (e : fordNativeGroup H) : (e.val w).im ≤ max w.im (1/w.im) := by
  obtain ⟨A,hA,he⟩ := (mem_fordNativeGroup H e.val).mp e.property
  rw [←he]
  exact discrete_unitTranslation_orbit_height_bound H hd hT A hA w

/-- Every actual integer translation belongs to the genuine native image of a group containing the unit translation. -/
theorem fordNativeGroup_integer_translation_mem (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ H) (n : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n : ℝ)) ∈ fordNativeGroup H := by
  apply (mem_fordNativeGroup H _).mpr
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n : ℝ),unitTranslation_integer_mem H hT
    n,rfl⟩

/-- In any genuine whole-group half-plane normalization containing a unit translation,
only finitely many actual horocyclic regions meet the actual closed locally finite domain. -/
theorem IsLocallyFiniteFuchsianDomain.normalized_horocyclic_images_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (k : ℝ) (hk : 0 < k) :
    {L : Set ℍ | ∃ g : fordNativeGroup
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H),
      L = (g.val : ℍ → ℍ) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k ∧
      (closure (fordSLNativeHom A '' (P.halfPlaneCoordinate '' D)) ∩ L).Nonempty}.Finite := by
  let N := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let F := fordSLNativeHom A
  let S := F '' (P.halfPlaneCoordinate '' D)
  have hEq := halfPlane_chart_whole_native_group P q hq A hA
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N := by
    let : DiscreteTopology H := P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  have hDc := ((isFuchsianFundamentalDomain_iff P D).mp hD.fundamental).2.1
  obtain ⟨w,hw⟩ := hDc.nonempty
  let z := F (P.halfPlaneCoordinate w)
  have hz : z ∈ S := ⟨P.halfPlaneCoordinate w,⟨w,hw,rfl⟩,rfl⟩
  apply native_horocyclic_region_images_finite (fordNativeGroup N) S
    ((hDc.image _ P.halfPlaneCoordinate.continuous.continuousOn).image _
      F.continuous.continuousOn) z hz
  · intro K hK
    have hf := hD.native_conjugate_compact_hits_finite F K hK
    change {e : fordNativeGroup N | ((e.val : ℍ → ℍ) '' closure S ∩ K).Nonempty}.Finite
    rw [show fordNativeGroup N = nativeConjugateGroup F P.halfPlaneActionHom.range from hEq]
    exact hf
  · exact fordNativeGroup_integer_translation_mem N hT
  · exact fordNativeGroup_orbit_height_bound N hd hT z
  · exact hk

/-- The actual original Mobius images of every genuine normalized horocyclic region have finite closed-domain incidence. -/
theorem IsLocallyFiniteFuchsianDomain.halfPlane_chart_horocyclic_images_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) (k : ℝ) (hk : 0 < k) :
    (fuchsianRegionImages P D
      (P.halfPlaneCoordinate.symm '' ((fordSLNativeHom A).symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k))).Finite := by
  let F := fordSLNativeHom A
  let ψ : P.domain.carrier ≃ₜ ℍ := P.halfPlaneCoordinate.trans F.toHomeomorph
  let G := fordNativeGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
  have hEq := halfPlane_chart_whole_native_group P q hq A hA
  let E : H → G := fun g => ⟨MulAut.conj F (P.halfPlaneAction g),by
    rw [show G = nativeConjugateGroup F P.halfPlaneActionHom.range from hEq]
    exact ⟨P.halfPlaneAction g,⟨g,rfl⟩,rfl⟩⟩
  have haction (g : H) (u : P.domain.carrier) : (E g).val (ψ u) = ψ (g • u) := by
    change F (P.halfPlaneAction g (F.symm (F (P.halfPlaneCoordinate u)))) =
      F (P.halfPlaneCoordinate (g • u))
    rw [F.symm_apply_apply,P.halfPlaneAction_coordinate]
  have hs : F '' (P.halfPlaneCoordinate '' D) = ψ '' D := by rw [image_image]; rfl
  have hf := hD.normalized_horocyclic_images_finite q hq A hA hT k hk
  rw [hs] at hf
  have hK : P.halfPlaneCoordinate.symm '' (F.symm ''
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) =
      ψ.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k := by rw [image_image]; rfl
  rw [hK]
  apply (hf.image (fun L : Set ℍ => ψ.symm '' L)).subset
  rintro L ⟨g,rfl,x,hxD,w,hw,hgw⟩
  have him : ψ.symm '' ((E g).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) =
      g • (ψ.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k) := by
    change _ = (fun x : P.domain.carrier => g • x) '' (ψ.symm ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)
    rw [image_image,image_image]
    congr 1
    funext v
    apply ψ.injective
    rw [ψ.apply_symm_apply,←haction,ψ.apply_symm_apply]
  refine ⟨(E g).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k,⟨E g,rfl,ψ
    x,?_,?_⟩,him⟩
  · rw [←ψ.image_closure D]
    exact mem_image_of_mem ψ hxD
  · obtain ⟨v,hv,hvw⟩ := hw
    refine ⟨v,hv,?_⟩
    have hew : v = ψ w := by rw [←hvw,ψ.apply_symm_apply]
    rw [hew,haction]
    exact congrArg ψ hgw

/-- Every actual parabolic fixed point has a genuine normalized family of horocyclic regions,
each with positive finite original closed-domain incidence. -/
theorem IsLocallyFiniteFuchsianDomain.parabolic_horocyclic_images_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f.val)
    (ξ : OnePoint ℂ) (hfix : f.val.val ξ = ξ) :
    ∃ (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ),
      q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius ∧ q.val ξ = ∞ ∧
      ∀ k : ℝ, 0 < k →
        let K := P.halfPlaneCoordinate.symm '' ((fordSLNativeHom A).symm ''
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.horizontalHorocyclicRegion k)
        (fuchsianRegionImages P D K).Nonempty ∧ (fuchsianRegionImages P D K).Finite := by
  obtain ⟨q,hq,hT,hqξ⟩ := parabolic_unit_halfPlane_normalizer P f hf ξ hfix
  obtain ⟨A,hA⟩ := halfPlane_chart_real_lift q hq
  refine ⟨q,A,hq,hA,hqξ,?_⟩
  intro k hk
  refine ⟨hD.fundamental.regionImages_nonempty ?_,
    hD.halfPlane_chart_horocyclic_images_finite q hq A hA hT k hk⟩
  refine ⟨P.halfPlaneCoordinate.symm ((fordSLNativeHom A).symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (k+1) (by linarith))),?_⟩
  exact ⟨_,⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (k+1) (by linarith),by change k < k+1; linarith,rfl⟩,rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian
