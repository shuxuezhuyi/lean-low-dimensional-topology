/- Actual cusp census for the retained group. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCoreEquality
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCuspLabels
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureHoroballIntersection
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureAuxiliaryCuspRepresentatives
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise OnePoint
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

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "θ₀" => generalCoreTheta g orders s t
local notation "hθ₀" => generalCoreTheta_mem g orders s t ho hdef
local notation "ρ₀" => generalCoreAuxPairing g orders s t
local notation "hρ₀" => generalCoreAuxPairing_involutive g orders s t
local notation "hθρ₀" => generalCoreAuxPairing_angle_profile g orders s t
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "P₀" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "K₀" => generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb
local notation "D₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc
  (generalCoreTargetMobiusData g orders s t ho hdef d hd hb)
local notation "A₀" => cofiniteMixedTangentialMobiusGroup θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
local notation "AP₀" => cofiniteMixedTangentialHalfPlaneData θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
  (generalCoreAux_positive_angular_periods g orders s t ho hdef)
local notation "AD₀" => _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.asFuchsianDisc AP₀
local notation "E₀" => cofiniteMixedTangentialGroupEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
local notation "U₀" => generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I

/-- Membership of the original centre in a true retained saturation forces
the entire auxiliary tile label to be retained, by actual developing injectivity. -/
theorem generalCoreAux_center_in_targetSaturation_mem (a : (S₀).Generated)
    (ha : a.val UpperHalfPlane.I ∈ generalCoreTargetTileSaturation g orders s t ho hdef d hd hb) :
    a.val ∈ H₀ := by
  obtain ⟨b, hbH, y, hy, hby⟩ := mem_iUnion₂.mp ha
  let p : (P₀).Point := ⟨UpperHalfPlane.I, (P₀).interior_subset_carrier
    (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb)⟩
  let q : (P₀).Point := ⟨y, hy⟩
  let bA : (S₀).Generated := ⟨b, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb hbH⟩
  have hproj : (S₀).project (a, p) = (S₀).project (bA, q) := by
    apply generalCoreAux_evaluation_injective g orders s t ho hdef d hd hb
    exact hby.symm
  have he := (S₀).gluing_interior_rigid (((S₀).project_eq_iff _ _).mp hproj)
    (Or.inl (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb))
  have hab : a.val = b := congrArg (fun c : (S₀).Copy => c.1.val) he
  exact hab ▸ hbH

/-- Two actual auxiliary chambers which meet are equal; equality forces the
actual auxiliary element into the actual retained subgroup. -/
theorem generalCoreAux_chamber_intersection_mem (a : (S₀).Generated)
    (ha : ((a.val '' U₀) ∩ U₀).Nonempty) : a.val ∈ H₀ := by
  let W := generalCoreCutWallUnion g orders s t ho hdef d hd hb
  have hIW := generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _
    (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb)
  have hW : a.val '' W = W := generalCoreCutWallUnion_image g orders s t ho hdef d hd hb a.val a.property
  have hc : a.val '' U₀ = connectedComponentIn Wᶜ (a.val UpperHalfPlane.I) := by
    have h := a.val.toHomeomorph.image_connectedComponentIn (show UpperHalfPlane.I ∈ Wᶜ from hIW)
    change a.val '' connectedComponentIn Wᶜ UpperHalfPlane.I =
      connectedComponentIn (a.val '' Wᶜ) (a.val UpperHalfPlane.I) at h
    simpa only [generalCoreCutChamber, image_compl_eq a.val.bijective, hW] using h
  obtain ⟨z, hzA, hzU⟩ := ha
  have he : a.val '' U₀ = U₀ :=
    hc.trans ((connectedComponentIn_eq (hc ▸ hzA)).trans (connectedComponentIn_eq hzU).symm)
  apply generalCoreAux_center_in_targetSaturation_mem g orders s t ho hdef d hd hb a
  rw [generalCoreTargetTileSaturation_eq_chamber_closure]
  apply subset_closure
  rw [← he]
  exact mem_image_of_mem a.val (mem_connectedComponentIn hIW)

/-- Every actual target parabolic fixed point has its own actual real-SL
normalizing chart whose entire sufficiently high tail lies in the same Nielsen region. -/
theorem generalCoreTarget_parabolic_point_tail
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀)
    (p : fuchsianCyclicFixedPoints (D₀) .parabolic) :
    ∃ q : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ Y : ℝ,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q⁻¹)).val ∞ = p.val ∧
      ∀ z : ℍ, Y < (q • z).im → _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z ∈ (D₀).nielsenRegion hNE := by
  obtain ⟨f, hfK, hf, hfp⟩ := p.property.2
  obtain ⟨r, v, hv, hr, hrf, hrp⟩ :=
    original_parabolic_real_translation_normalizer (D₀) ⟨f, hfK⟩ hf
  obtain ⟨q, hq⟩ := mobius_preserves_halfPlane_exists_SL r hr
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (v : ℂ) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate r K₀ :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff r K₀ _).mpr ⟨f, hfK, hrf⟩
  refine ⟨q, |v| / 2, ?_, ?_⟩
  · rw [map_inv, hq]
    apply r.val.injective
    change r.val (r.val.symm ∞) = r.val p.val
    rw [r.val.apply_symm_apply, hrp p.val hfp]
  · intro z hz
    apply nielsenRegion_contains_normalized_translation_tail (D₀) hNE r hr v hv hT
    refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (q • z), ⟨q • z, hz, rfl⟩, ?_⟩
    change r.val.symm (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (q • z)) = _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z
    have hact : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (q • z) = r.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) :=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action q z).symm.trans (congrArg (fun k : Mobius.complexMobiusGroup =>
        k.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)) hq)
    rw [hact]
    exact r.val.symm_apply_apply _


/-- The actual faithful boundary images respect the actual native subgroup inclusion. -/
theorem generalCoreTargetMobiusGroup_le_aux : K₀ ≤ A₀ := by
  rintro f ⟨a, rfl⟩
  exact ⟨⟨a.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb a.property⟩, rfl⟩

/-- Every original zero corner is an actual target parabolic fixed point.
The parabolic is the actual retained ideal-cycle word. -/
theorem generalCoreTarget_zero_vertex_parabolic
    (i : Fin (generalCoreAngles g orders s t).length) (hi : θ₀ i = 0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm ((Q₀).vertices i)).val ∈
      fuchsianCyclicFixedPoints (D₀) .parabolic := by
  let τ := (ρ₀).trans (finRotate _)
  let N := orderOf τ
  have hreturn : (τ ^ N) i = i := by rw [pow_orderOf_eq_one]; rfl
  obtain ⟨A, hword, _haux, hpar, hfix⟩ := cofiniteTangential_zero_period_parabolic_fixer
    θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ i hi N (orderOf_pos τ) hreturn
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ H₀ := by
    rw [hword]
    exact generalCoreTargetIdealWord_mem g orders s t ho hdef d hd hb i hi N
  refine ⟨(by intro h; cases h), _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, ?_, hpar, hfix⟩
  exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩, nativeConformalSubgroupMobiusHom_matrix H₀
    (generalCoreTargetGroup_conformal g orders s t ho hdef d hd hb) A hA⟩

/-- An auxiliary incidence between any two actual target cusp points is
already a target incidence. The whole two groups and all cusp points are used. -/
theorem generalCoreTarget_cusp_incidence_mem
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀)
    (p q : fuchsianCyclicFixedPoints (D₀) .parabolic) (a : A₀)
    (ha : a.val.val q.val = p.val) : a.val ∈ K₀ := by
  obtain ⟨r, Y, hr, hrN⟩ := generalCoreTarget_parabolic_point_tail g orders s t ho hdef d hd hb hNE p
  obtain ⟨v, Z, hv, hvN⟩ := generalCoreTarget_parabolic_point_tail g orders s t ho hdef d hd hb hNE q
  obtain ⟨B, hB⟩ := mobius_preserves_halfPlane_exists_SL a.val ((AP₀).preserves a)
  let aN : (S₀).Generated := (E₀).symm a
  have hBnative : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B = aN.val := by
    apply IsometryEquiv.ext
    intro z
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    have hact := nativeConformalSubgroupMobiusHom_action (S₀).Generated
      (cofiniteMixedTangentialGenerated_conformal θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀) aN z
    have hea : cofiniteMixedTangentialToMobius θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ aN = a.val :=
      congrArg Subtype.val ((E₀).apply_symm_apply a)
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (B • z) = _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (aN.val z)
    change (cofiniteMixedTangentialToMobius θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ aN).val
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) = _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (aN.val z) at hact
    rw [hea] at hact
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action B z).symm.trans
      ((congrArg (fun k : Mobius.complexMobiusGroup => k.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)) hB).trans hact)
  have hcenter : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((r * B)⁻¹)).val ∞ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (v⁻¹)).val ∞ := by
    rw [mul_inv_rev, map_mul]
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B⁻¹)).val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (r⁻¹)).val ∞) = _
    rw [hr, hv, map_inv, hB]
    change a.val.val.symm p.val = q.val
    exact a.val.val.injective ((a.val.val.apply_symm_apply p.val).trans ha.symm)
  obtain ⟨z, hzR, hzV⟩ := generalSignature_same_cusp_tails_intersect (r * B) v hcenter Y Z
  have hzN : z ∈ _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE := hvN z hzV
  have hazN : aN.val z ∈ _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' (D₀).nielsenRegion hNE := by
    rw [← hBnative]
    apply hrN
    change Y < (r • (B • z)).im
    simpa only [mul_smul] using hzR
  have hU := generalCoreTarget_chamber_eq_nielsen g orders s t ho hdef d hd hb hNE
  have haH : aN.val ∈ H₀ := generalCoreAux_chamber_intersection_mem g orders s t ho hdef d hd hb
    aN ⟨aN.val z, ⟨z, hU.symm ▸ hzN, rfl⟩, hU.symm ▸ hazN⟩
  refine ⟨⟨aN.val, haH⟩, ?_⟩
  exact congrArg Subtype.val ((E₀).apply_symm_apply a)

/-- The complete auxiliary cusp count equals the source number of original
zero labels; the whole natural ideal-corner relation is used. -/
theorem generalCoreAux_parabolic_classes_card :
    Nat.card (FuchsianCyclicConjugacyClasses (AD₀) .parabolic) = s := by
  let I := {i : Fin (generalCoreAngles g orders s t).length // ‖((Q₀).vertices i : ℂ)‖ = 1}
  let R := (Relation.EqvGen.setoid (fun a b : Fin (generalCoreAngles g orders s t).length =>
    b = finRotate _ (ρ₀ a))).comap (Subtype.val : I → _)
  have hzero (i : I) : θ₀ i.val = 0 :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff θ₀ d hθ₀ hd i.val).mp i.property
  have hi : Function.Injective (fun i : I => (Quotient.mk R i : Quotient R)) := by
    intro a b hab
    obtain ⟨j, hj⟩ := (generalCoreTheta_zero_iff g orders s t ho hdef a.val).mp (hzero a)
    have hrel := Quotient.exact hab
    change Relation.EqvGen (fun a b => b = finRotate _ (ρ₀ a)) a.val b.val at hrel
    rw [← hj] at hrel
    exact Subtype.ext (hj.symm.trans ((generalCoreCuspIndex_class_singleton g orders s t j b.val).mp hrel).symm)
  let EI : I ≃ Quotient R := Equiv.ofBijective (fun i => Quotient.mk R i) ⟨hi, Quotient.mk_surjective⟩
  let EZ : I ≃ {i : Fin (generalCoreAngles g orders s t).length // θ₀ i = 0} :=
    Equiv.subtypeEquivRight (fun i => _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff θ₀ d hθ₀ hd i)
  obtain ⟨EC⟩ := cofiniteMixedTangential_ideal_cusp_classes_equiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
    (generalCoreAux_positive_angular_periods g orders s t ho hdef)
  have hc : Nat.card (FuchsianCyclicConjugacyClasses (AP₀).cayleyData.asFuchsianDisc .parabolic) = s :=
    (Nat.card_congr EC.symm).trans ((Nat.card_congr EI.symm).trans
      ((Nat.card_congr EZ).trans (generalCore_zero_angle_card g orders s t ho hdef)))
  have hdisc : (AP₀).cayleyData.asFuchsianDisc = (AD₀).nielsenConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius := by
    apply _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.eq_of_carrier_eq
    exact cayleyMobius_image_openHalfPlane.symm
  rw [hdisc] at hc
  exact (fuchsianCyclicClassConjugacyEquiv_natCard (AD₀) .parabolic _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).symm.trans hc


/-- Inclusion of actual target parabolic fixed points into the actual whole
auxiliary group preserves their literal sphere coordinates. -/
def generalCoreTargetCuspPointInclusion (p : fuchsianCyclicFixedPoints (D₀) .parabolic) :
    fuchsianCyclicFixedPoints (AD₀) .parabolic :=
  ⟨p.val, by
    obtain ⟨f, hfK, hf, hfp⟩ := p.property.2
    exact ⟨(by intro h; cases h), f,
      generalCoreTargetMobiusGroup_le_aux g orders s t ho hdef d hd hb hfK, hf, hfp⟩⟩

/-- The map uses the whole actual orbit relations on both sides. -/
def generalCoreTargetCuspOrbitMap :
    MulAction.orbitRel.Quotient K₀ (fuchsianCyclicFixedPoints (D₀) .parabolic) →
      MulAction.orbitRel.Quotient A₀ (fuchsianCyclicFixedPoints (AD₀) .parabolic) :=
  Quotient.map (generalCoreTargetCuspPointInclusion g orders s t ho hdef d hd hb) (by
    intro p q hpq
    change MulAction.orbitRel K₀ (fuchsianCyclicFixedPoints (D₀) .parabolic) p q at hpq
    change MulAction.orbitRel A₀ (fuchsianCyclicFixedPoints (AD₀) .parabolic) _ _
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq ⊢
    obtain ⟨a, ha⟩ := hpq
    have hsphere : a.val.val q.val = p.val := congrArg Subtype.val ha
    exact ⟨⟨a.val, generalCoreTargetMobiusGroup_le_aux g orders s t ho hdef d hd hb a.property⟩,
      Subtype.ext hsphere⟩)

/-- Auxiliary conjugacy cannot merge any two actual target cusp classes. -/
theorem generalCoreTargetCuspOrbitMap_injective
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    Function.Injective (generalCoreTargetCuspOrbitMap g orders s t ho hdef d hd hb) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro p q he
  have hrel := Quotient.exact he
  change MulAction.orbitRel A₀ (fuchsianCyclicFixedPoints (AD₀) .parabolic)
    (generalCoreTargetCuspPointInclusion g orders s t ho hdef d hd hb p)
    (generalCoreTargetCuspPointInclusion g orders s t ho hdef d hd hb q) at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨a, ha⟩ := hrel
  have hsphere : a.val.val q.val = p.val := congrArg Subtype.val ha
  have hamem := generalCoreTarget_cusp_incidence_mem g orders s t ho hdef d hd hb hNE p q a hsphere
  apply Quotient.sound
  change MulAction.orbitRel K₀ (fuchsianCyclicFixedPoints (D₀) .parabolic) p q
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨⟨a.val, hamem⟩, Subtype.ext hsphere⟩

/-- Every whole-auxiliary cusp class contains an actual target cusp. The
representative is an original zero corner and its actual retained parabolic word. -/
theorem generalCoreTargetCuspOrbitMap_surjective :
    Function.Surjective (generalCoreTargetCuspOrbitMap g orders s t ho hdef d hd hb) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro p
  obtain ⟨f, hfA, hf, hfp⟩ := p.property.2
  obtain ⟨a, i, hi, hap⟩ := mixedTangential_parabolic_fixedPoint_zero_corner θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
    (generalCoreAux_positive_angular_periods g orders s t ho hdef) ⟨f, hfA⟩ hf p.val hfp
  let q : fuchsianCyclicFixedPoints (D₀) .parabolic :=
    ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm ((Q₀).vertices i)).val,
      generalCoreTarget_zero_vertex_parabolic g orders s t ho hdef d hd hb i hi⟩
  refine ⟨Quotient.mk _ q, Quotient.sound ?_⟩
  change MulAction.orbitRel A₀ (fuchsianCyclicFixedPoints (AD₀) .parabolic) _ p
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨a, Subtype.ext hap⟩

/-- The actual retained subgroup and the actual auxiliary group have the
same entire parabolic conjugacy-class set, although their other end data differ. -/
def generalCoreTargetParabolicClassEquivAux
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    FuchsianCyclicConjugacyClasses (D₀) .parabolic ≃
      FuchsianCyclicConjugacyClasses (AD₀) .parabolic :=
  (fuchsianCyclicConjugacyClassesEquiv (D₀) .parabolic).trans
    ((Equiv.ofBijective (generalCoreTargetCuspOrbitMap g orders s t ho hdef d hd hb)
      ⟨generalCoreTargetCuspOrbitMap_injective g orders s t ho hdef d hd hb hNE,
        generalCoreTargetCuspOrbitMap_surjective g orders s t ho hdef d hd hb⟩).trans
      (fuchsianCyclicConjugacyClassesEquiv (AD₀) .parabolic).symm)

/-- Exactly the original s cusp occurrences are the full actual parabolic
conjugacy classes of the actual target group. Exhaustion and nonmerging are proved. -/
theorem generalCoreTarget_parabolic_classes_card
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K₀) :
    Nat.card (FuchsianCyclicConjugacyClasses (D₀) .parabolic) = s :=
  (Nat.card_congr (generalCoreTargetParabolicClassEquivAux g orders s t ho hdef d hd hb hNE)).trans
    (generalCoreAux_parabolic_classes_card g orders s t ho hdef d hd hb)

end LowDimensionalTopology.Geometry.Fuchsian
