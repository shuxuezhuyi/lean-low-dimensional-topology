/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnCovering
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.PolygonVertexAngularMultiplicity
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.SmallLambdaTriangleReduction
public import Mathlib.GroupTheory.GroupAction.Quotient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal MatrixGroups OnePoint
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

/-- Actual finite translate labels invariant under a subgroup split into free
left-multiplication orbits of the subgroup's full cardinality. -/
theorem halfTurn_incident_labels_card_dvd {G : Type*} [Group G]
    (S : Subgroup G) (T : Set G) (hT : T.Finite)
    (hInv : ∀s : S,∀g∈T,(s : G)*g∈T) : Nat.card S ∣ Nat.card T := by
  classical
  let _finiteLabels : Finite T := hT.to_subtype
  let labelsAction : MulAction S T := {
    smul := fun s g=>⟨(s : G)*g.val,hInv s g.val g.property⟩
    one_smul := fun g=>Subtype.ext (one_mul g.val)
    mul_smul := fun s t g=>Subtype.ext (mul_assoc (s : G) (t : G) g.val) }
  have hFree (g : T) : MulAction.stabilizer S g=⊥ := by
    ext s
    rw [MulAction.mem_stabilizer_iff,Subgroup.mem_bot]
    constructor
    · intro hs
      apply Subtype.ext
      have he:=congrArg Subtype.val hs
      change (s : G)*g.val=g.val at he
      exact mul_right_cancel (he.trans (one_mul g.val).symm)
    · rintro rfl
      exact one_smul S g
  let e:=MulAction.selfEquivOrbitsQuotientProd (G:=S) (X:=T) hFree
  have he:=Nat.card_congr e
  rw [Nat.card_prod] at he
  exact ⟨Nat.card (Quotient (MulAction.orbitRel S T)),by simpa only [mul_comm] using he⟩

/-- The actual labels mapping a fixed point into a chosen region are invariant
under its full original stabilizer; no geometric multiplicity is postulated. -/
theorem halfTurn_point_region_labels_card_dvd
    (H : Subgroup (ℍ≃ᵢℍ)) (z : ℍ) (R : Set ℍ)
    (hR : {g : H | g⁻¹ • z∈R}.Finite) :
    Nat.card (MulAction.stabilizer H z) ∣ Nat.card {g : H | g⁻¹ • z∈R} := by
  apply halfTurn_incident_labels_card_dvd _ _ hR
  intro s g hg
  change ((s.val*g)⁻¹) • z∈R
  rw [mul_inv_rev,mul_smul]
  have hs : s.val⁻¹ • z=z := by
    have he:=congrArg (fun x : ℍ=>s.val⁻¹ • x) s.property
    simpa only [MulAction.mem_stabilizer_iff,inv_smul_smul] using he.symm
  rwa [hs]

/-- Away from the actual vertices of a finite native polygon, twice each
genuine angular fraction counts two inside labels or one side label. -/
theorem halfTurn_nonvertex_double_angular_fraction
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ}
    {V : Set ℍ}
    (D : _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (hP : IsCompact P.carrier) (x : ℍ) (hx : x∉V) :
    (2 : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x=
      P.interior.indicator (fun _ : ℍ=>(2 : ℝ≥0∞)) x+
        (P.carrier\P.interior).indicator (fun _ : ℍ=>(1 : ℝ≥0∞)) x := by
  classical
  by_cases hi : x∈P.interior
  · have hI : x∈interior P.carrier := by rwa [D.carrier_closure,D.regular_open]
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction_of_interior hI,indicator_of_mem hi,
      indicator_of_notMem (by simp only [Set.mem_sdiff,hi,not_true_eq_false,and_false,not_false_eq_true])]
    simp
  · rw [indicator_of_notMem hi]
    by_cases hc : x∈P.carrier
    · rw [indicator_of_mem (show x∈P.carrier\P.interior from ⟨hc,hi⟩),zero_add]
      have hb : x∈P.boundary := (show x∈P.interior ∨ x∈P.boundary from hc).resolve_left hi
      obtain ⟨s,hs,hxs⟩:=mem_sUnion.mp hb
      have ha:=D.nonvertex_localAngle ⟨x,hc⟩ ⟨s,hs⟩ hxs hx
      have hfr : _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x≠⊤ :=
        ne_top_of_le_ne_top (by simp) (_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction_le_one _ _)
      apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by simp) hfr) (by simp)).mp
      rw [ENNReal.toReal_mul]
      norm_num only [ENNReal.toReal_ofNat,ENNReal.toReal_one]
      unfold _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle at ha
      nlinarith [Real.pi_pos]
    · rw [indicator_of_notMem (show x∉P.carrier\P.interior from fun h=>hc h.1),zero_add]
      rw [_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction_of_not_mem_closure (by rwa [hP.isClosed.closure_eq])]
      simp


/-- The same free actual label action divides a sum of invariant natural
weights, by partitioning its actual finite label set into weight fibers. -/
theorem halfTurn_incident_labels_weighted_sum_dvd {G : Type*} [Group G]
    (S : Subgroup G) (I : Finset G)
    (hInv : ∀s : S,∀g∈I,(s : G)*g∈I)
    (w : G→ℕ) (hw : ∀s : S,∀g∈I,w ((s : G)*g)=w g) :
    Nat.card S ∣ ∑g∈I,w g := by
  classical
  have hDiv (n : ℕ) : Nat.card S ∣ (I.filter (fun g=>w g=n)).card := by
    have hh:=halfTurn_incident_labels_card_dvd S
      (↑(I.filter (fun g=>w g=n)) : Set G) (Finset.finite_toSet _)
      (by
        intro s g hg
        rcases Finset.mem_filter.mp hg with ⟨hg,he⟩
        exact Finset.mem_filter.mpr ⟨hInv s g hg,(hw s g hg).trans he⟩)
    simpa only [Nat.card_coe_set_eq,Set.ncard_coe_finset] using hh
  have hSum:=Finset.sum_fiberwise_of_maps_to' (s:=I) (t:=I.image w) (g:=w)
    (fun g hg=>Finset.mem_image_of_mem w hg) (fun n : ℕ=>n)
  rw [←hSum]
  apply Finset.dvd_sum
  intro n _
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact dvd_mul_of_dvd_left (hDiv n) n

/-- A natural common denominator for the actual local angular fractions on
one real orbit makes the true stabilizer order divide that denominator
times the true covering multiplicity. -/
theorem halfTurn_actual_angular_denominator_dvd
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (P : Set ℍ) (hP : IsCompact P) (z : ℍ) (d N : ℕ)
    (hN : _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity H P z=N)
    (hIntegral : ∀g : H,∃m : ℕ,(d : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P (g⁻¹ • z)=m) :
    Nat.card (MulAction.stabilizer H z) ∣ d*N := by
  classical
  let I:=((native_compact_translates_locallyFinite H hP).point_finite z).toFinset
  let w : H→ℕ:=fun g=>(hIntegral g).choose
  have hw (g : H) : (d : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P (g⁻¹ • z)=w g :=
    (hIntegral g).choose_spec
  have hI (g : H) : g∈I ↔g⁻¹ • z∈P := by
    rw [Set.Finite.mem_toFinset]
    exact mem_smul_set_iff_inv_smul_mem
  have hFix (s : MulAction.stabilizer H z) : s.val⁻¹ • z=z := by
    have hs : s.val • z=z:=s.property
    simpa only [inv_smul_smul] using congrArg (fun x : ℍ=>s.val⁻¹ • x) hs.symm
  have hPoint (s : MulAction.stabilizer H z) (g : H) :
      (s.val*g)⁻¹ • z=g⁻¹ • z := by rw [mul_inv_rev,mul_smul,hFix]
  have hDiv:=halfTurn_incident_labels_weighted_sum_dvd
    (MulAction.stabilizer H z) I
    (by intro s g hg;rw [hI,hPoint];exact (hI g).mp hg)
    w (by
      intro s g _
      apply (Nat.cast_inj (R:=ℝ≥0∞)).mp
      rw [←hw,←hw,hPoint])
  have hEq : (d*N : ℕ)=(∑g∈I,w g) := by
    have he : (d : ℝ≥0∞)*(N : ℝ≥0∞)=∑g∈I,(w g : ℝ≥0∞) := by
      rw [←hN, _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity_eq_sum_incident H P hP z,
        Finset.mul_sum]
      exact Finset.sum_congr rfl (fun g _=>hw g)
    exact_mod_cast he
  rwa [hEq]

/-- At every actual canonical quadrilateral point except its two summits,
the actual local angular fraction has a denominator dividing four. The
right-angle axis corners are included, without inventing halfturn fixers
at those arbitrary axis positions. -/
theorem halfTurnCanonical_quarter_angular_fraction
    (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) (x : ℍ)
    (h2 : x≠_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
      (halfTurnQuadCanonical_finite k c hk hc) 2)
    (h3 : x≠_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
      (halfTurnQuadCanonical_finite k c hk hc) 3) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    ∃m : ℕ,(4 : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x=m := by
  classical
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let D:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_native_geometry Q hf
  have hP:IsCompact P.carrier:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf
  have hfrac : _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x≠⊤:=
    ne_top_of_le_ne_top (by simp) (_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction_le_one _ _)
  have hRight (ha : _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle P.interior x=Real.pi/2) :
      (4 : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x=1 := by
    unfold _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle at ha
    rw [D.localAngularFraction_interior_eq hP x] at ha
    apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by simp) hfrac) (by simp)).mp
    rw [ENNReal.toReal_mul]
    norm_num only [ENNReal.toReal_ofNat,ENNReal.toReal_one]
    nlinarith [Real.pi_pos]
  by_cases hv : x∈range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf)
  · obtain ⟨i,rfl⟩:=hv
    have hAngle:=finitePolygon_nativeLocalAngle_at_vertex Q hf
      (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon_isConvex i
    have hAngles:=halfTurnQuadCanonical_angles k c hk hc
    fin_cases i
    · exact ⟨1,by simpa only [Nat.cast_one] using hRight (hAngle.trans hAngles.2.2.1)⟩
    · exact ⟨1,by simpa only [Nat.cast_one] using hRight (hAngle.trans hAngles.2.2.2.1)⟩
    · exact (h2 rfl).elim
    · exact (h3 rfl).elim
  · have he:=halfTurn_nonvertex_double_angular_fraction D hP x hv
    by_cases hi : x∈P.interior
    · rw [indicator_of_mem hi,
        indicator_of_notMem (show x∉P.carrier\P.interior from fun h=>h.2 hi),add_zero] at he
      refine ⟨4,?_⟩
      calc
        (4 : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x=
          2*(2*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x):=by ring
        _=4:=by rw [he];norm_num
    · rw [indicator_of_notMem hi,zero_add] at he
      by_cases hc' : x∈P.carrier
      · rw [indicator_of_mem (show x∈P.carrier\P.interior from ⟨hc',hi⟩)] at he
        refine ⟨2,?_⟩
        calc
          (4 : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x=
            2*(2*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x):=by ring
          _=2:=by rw [he];norm_num
      · rw [indicator_of_notMem (show x∉P.carrier\P.interior from fun h=>hc' h.1)] at he
        refine ⟨0,?_⟩
        simp only [Nat.cast_zero]
        calc
          (4 : ℝ≥0∞)*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x=
            2*(2*_root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngularFraction P.carrier x):=by ring
          _=0:=by rw [he];norm_num


/-- The faithful boundary representation preserves the full physical point
stabilizer, not only the orders of selected elliptic elements. -/
theorem halfTurn_native_stabilizer_card
    (H : Subgroup (ℍ≃ᵢℍ))
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (z : ℍ) :
    Nat.card (MulAction.stabilizer H z)=
      Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (nativeConformalSubgroupMobiusHom H hConf).range
        (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)) := by
  let F:=nativeConformalSubgroupMobiusHom H hConf
  let S:=MulAction.stabilizer H z
  let f:=F.comp S.subtype
  have hf : Function.Injective f :=
    (nativeConformalSubgroupMobiusHom_isometry H hConf).injective.comp Subtype.val_injective
  have hRange : f.range=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer F.range (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z) := by
    ext a
    constructor
    · rintro ⟨s,rfl⟩
      apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ _).mpr
      refine ⟨⟨s.val,rfl⟩,?_⟩
      change (nativeConformalSubgroupMobiusHom H hConf s.val).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=_
      rw [nativeConformalSubgroupMobiusHom_action]
      exact congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint s.property
    · intro ha
      obtain ⟨ha,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ _).mp ha
      obtain ⟨g,rfl⟩:=ha
      have hg : g∈S := by
        apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
        exact (nativeConformalSubgroupMobiusHom_action H hConf g z).symm.trans hfix
      exact ⟨⟨g,hg⟩,rfl⟩
  let e:=MonoidHom.ofInjective hf
  have he:=Nat.card_congr e.toEquiv
  rwa [hRange] at he

/-- An actual listed cone of order three supplies an actual native point
whose full original stabilizer has order three. -/
theorem halfTurn_actual_signature_three_point
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    {g p : ℕ} {orders : List ℕ}
    (hSig : HasCofiniteFuchsianSignature
      (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc g orders p)
    (hThree : 3∈orders) : ∃z : ℍ,Nat.card (MulAction.stabilizer H z)=3 := by
  let F:=nativeConformalSubgroupMobiusHom H hConf
  let P:=nativeConformalSubgroup_halfPlaneData H hConf
  let D:=P.asFuchsianDisc
  obtain ⟨c,hc⟩:=hSig.mem_orders.mp hThree
  obtain ⟨M,rfl⟩:=Quotient.exists_rep c
  change Nat.card M.val=3 at hc
  obtain ⟨a,haM,ha⟩:=M.property.2
  have haH : a∈F.range:=M.property.1.1 haM
  obtain ⟨x,hax,_⟩:=elliptic_disc_existsUnique_fixed a ha D.isDisc (D.image_eq ⟨a,haH⟩)
  have hM : M.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer F.range x.val :=
    maximal_elliptic_cyclic_eq_stabilizer D M.property.1 a haM ha x hax
  have hx : x.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=x.property
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range] at hx
  obtain ⟨z,hz⟩:=hx
  refine ⟨z,?_⟩
  rw [halfTurn_native_stabilizer_card H hConf z,hz,←hM]
  exact hc

/-- A genuine order larger than three fixing one physical point excludes
that entire orbit from a point with full stabilizer order three. -/
theorem halfTurn_cone_three_orbit_avoids_large_order_fixed
    (H : Subgroup (ℍ≃ᵢℍ)) (z x : ℍ)
    (hstab : Nat.card (MulAction.stabilizer H z)=3)
    (a : H) (ha : a • x=x) (horder : 3<orderOf a) :
    ∀g : H,g⁻¹ • z≠x := by
  intro g he
  let e:=MulAction.stabilizerEquivStabilizer (g:=g⁻¹) (a:=z) (b:=x) he.symm
  have hcard : Nat.card (MulAction.stabilizer H x)=3 :=
    (Nat.card_congr e.toEquiv).symm.trans hstab
  let _finiteStabilizer : Finite (MulAction.stabilizer H x):=
    Nat.finite_of_card_ne_zero (by rw [hcard];decide)
  let b : MulAction.stabilizer H x:=⟨a,ha⟩
  have hd:=orderOf_dvd_natCard b
  have hb : orderOf b=orderOf a:=
    (orderOf_injective (MulAction.stabilizer H x).subtype Subtype.val_injective b).symm
  rw [hb,hcard] at hd
  have hh:=Nat.le_of_dvd (by decide : 0<3) hd
  omega

/-- The unchanged actual nonprimitive construction retains its literal
whole-group angular sum as well as its actual signature and area. This
extends the interface of the existing proof without changing its argument. -/
theorem halfTurnCanonical_nonprimitive_signature_with_multiplicity
    (u t : ℝ) (hu : 1≤u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
          (zero_lt_one.trans (hu.trans_lt hut)))),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set Mobius.complexMobiusGroup)))
    (p q : ℕ) (hp : 2≤p) (hpq : 2*p<q)
    (hq : q=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
        (zero_lt_one.trans (hu.trans_lt hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)))
    (hθ : Real.arccos (halfTurnQuadKleinB (t^2) (t^2/w.re)/
      Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
        (halfTurnQuadKleinA (t^2) (t^2/w.re))^2))=Real.pi*p/q) :
    let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)
    let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
      (zero_lt_one.trans (hu.trans_lt hut)))
    let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
    let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
    letI:=threeHalfTurn_native_group_discrete_of_original F G W hd
    let hConf:=threeHalfTurn_native_group_conformal F G W
    let P:=nativeConformalSubgroup_halfPlaneData H hConf
    ∃orders : List ℕ,HasCofiniteFuchsianSignature P.asFuchsianDisc 0 orders 0 ∧
      orders.length=3 ∧
      ∃N n : ℕ,0<N ∧ p≤N ∧ n∈orders ∧ q∣n ∧
        2*(N : ℝ)*(-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum)=1-2*(p : ℝ)/q ∧
        (∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity H
          (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon
            (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
              (one_lt_pow₀ (hu.trans_lt hut) (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
            (halfTurnQuadCanonical_finite _ _ _ _)).interior z=N) := by
  let hu0:=zero_lt_one.trans_le hu
  let ht:=hu.trans_lt hut
  let ht0:=zero_lt_one.trans ht
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu0
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu0 ht0)
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  let K:=F*G*W
  let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
  let : DiscreteTopology H:=threeHalfTurn_native_group_discrete_of_original F G W hd
  let hConf:=threeHalfTurn_native_group_conformal F G W
  let P:=nativeConformalSubgroup_halfPlaneData H hConf
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let z:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
  let y:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2
  let lam:=halfTurnQuadKleinB (t^2) (t^2/w.re)/
    Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
      (halfTurnQuadKleinA (t^2) (t^2/w.re))^2)
  obtain ⟨N,hN,hCount,_hLow,hArea⟩:=halfTurnCanonical_cover_multiplicity u t hu hut w hw hn hc
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F∈H:=Subgroup.subset_closure (by simp)
  have hG : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G∈H:=Subgroup.subset_closure (by simp)
  have hW : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W∈H:=Subgroup.subset_closure (by simp)
  let a : H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W,H.mul_mem (H.mul_mem hF hG) hW⟩
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht0))∈H:=by
    rw [←halfTurnNative_axis_product u t hu0 ht0]
    exact H.mul_mem hG hF
  let d : H:=⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht0)))⁻¹,H.inv_mem hD⟩
  have hfix : a•z=z:=halfTurnCanonical_product_fixes_summit u t hu0 ht w hw hn hc
  have hmove : d⁻¹•z=y:=by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht0)))⁻¹)⁻¹ z=y
    rw [inv_inv]
    exact halfTurnFour_summit_dilation (t^2) (t^2/w.re) hk hc w hw hn rfl
  have hprod : a.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K:=by
    apply IsometryEquiv.ext
    intro x
    change F•(G•(W•x))=(F*G*W)•x
    simp only [mul_smul]
  have horder : orderOf a=q:=by
    calc
      orderOf a=orderOf a.val:=(orderOf_injective H.subtype Subtype.val_injective a).symm
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K):=by rw [hprod]
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K):=hSLIsometry_orderOf_eq_realSLMobius K
      _=q:=hq.symm
  have hb:=halfTurnQuadCanonical_angles (t^2) (t^2/w.re) hk hc
  have hzAngle : _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle R.interior z=Real.arccos lam:=
    (finitePolygon_nativeLocalAngle_at_vertex Q hf
      (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon_isConvex 3).trans
      hb.2.2.2.2.2
  have hyAngle : _root_.LowDimensionalTopology.Geometry.Polygon.nativeLocalAngle R.interior y=Real.arccos lam:=
    (finitePolygon_nativeLocalAngle_at_vertex Q hf
      (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon_isConvex 2).trans
      hb.2.2.2.2.1
  have hqR : 0<(q : ℝ):=by exact_mod_cast (show 0<q by omega)
  have hθq : Real.arccos lam*(q : ℝ)=Real.pi*p:=by
    rw [hθ]
    field_simp
  have hDegree:=halfTurn_two_summit_degree_lower H R.interior a d z y hfix hmove
    (halfTurnFour_summits_ne (t^2) (t^2/w.re) hk hc) p q N horder
    (Real.arccos lam) hθq hzAngle hyAngle (hCount z)
  have hcover (x : ℍ) : ∃g : H,g•x∈R.carrier:=by
    obtain ⟨b,hb,hqb⟩:=halfTurnClosedQuad_meetsEveryOrbit H (t^2) hk hD u hu0 hF w hw hW x
    rcases hb with ⟨g,rfl⟩
    refine ⟨g,?_⟩
    apply (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier_iff Q hf _).mpr
    apply (halfTurnQuadCanonical_native_closedCarrier (t^2) (t^2/w.re) hk hc _).mpr
    simpa [halfTurnClosedQuad,halfTurnQuadCirclePolynomial,hn,
      div_mul_eq_mul_div,mul_div_assoc] using hqb
  obtain ⟨g,orders,hSig,hCov,_hCovPos,_hCovFin,hCovRealPos⟩:=
    compactSignature_native_compact_cover H hConf R.carrier
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf) hcover
  let e:=nativeCovolume_groupEquiv H hConf
  have heK : (e a).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K:=by
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K∈H:=hprod ▸ a.property
    have ha : a=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K,hm⟩:=Subtype.ext hprod
    change nativeConformalSubgroupMobiusHom H hConf a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K
    rw [ha,nativeConformalSubgroupMobiusHom_matrix]
  have hEllipse : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K):=by
    by_contra he
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_not_elliptic_abs_trace K he
    have htrace : |Matrix.trace K.val|=2*lam:=by
      rw [halfTurnCanonical_trace u t hu0 ht w hw hn,abs_of_pos (mul_pos (by norm_num) hb.1)]
    rw [htrace] at hh
    linarith only [hh,hb.2.1]
  have hE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (e a).val:=by rw [heK];exact hEllipse
  obtain ⟨n,hnmem,hdiv⟩:=elliptic_order_dvd_signature_entry P.asFuchsianDisc (e a) hE hSig
  have heorder : orderOf (e a)=q:=
    (orderOf_injective e.toMonoidHom e.injective a).trans horder
  rw [heorder] at hdiv
  have hqn : q≤n:=Nat.le_of_dvd (by have hh:=hSig.orders_two_le hnmem;omega) hdiv
  let δ:=2*(g : ℝ)-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum
  have hδpos : 0<δ:=by
    rw [hCov] at hCovRealPos
    exact (mul_pos_iff_of_pos_left (show 0<2*Real.pi by positivity)).mp hCovRealPos
  have hAreaScalar : 2*(N : ℝ)*δ=1-2*(p : ℝ)/q:=by
    rw [hCov,hθ] at hArea
    apply (mul_left_cancel₀ Real.pi_ne_zero)
    calc
      Real.pi*(2*(N : ℝ)*δ)=(N : ℝ)*(2*Real.pi*δ):=by ring
      _=Real.pi-2*(Real.pi*p/q):=hArea.symm
      _=Real.pi*(1-2*(p : ℝ)/q):=by ring
  have hStructure:=halfTurn_cover_small_signature_structure g orders (fun _ hm=>hSig.orders_two_le hm)
    p q N n hp hpq hDegree hnmem hqn hδpos hAreaScalar
  rcases hStructure with ⟨rfl,hlen⟩
  refine ⟨orders,hSig,hlen,N,n,hN,hDegree,hnmem,hdiv,?_,hCount⟩
  simpa only [δ,Nat.cast_zero,mul_zero,zero_sub] using hAreaScalar


/-- The source canonical group has its actual angular multiplicity divisible
by three whenever its actual resulting cone list contains three. All area
and signature data and the multiplicity itself are derived. -/
theorem halfTurnCanonical_nonprimitive_signature_cone_divisibility
    (u t : ℝ) (hu : 1≤u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
          (zero_lt_one.trans (hu.trans_lt hut)))),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set Mobius.complexMobiusGroup)))
    (p q : ℕ) (hp : 2≤p) (hpq : 2*p<q)
    (hq : q=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
        (zero_lt_one.trans (hu.trans_lt hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)))
    (hθ : Real.arccos (halfTurnQuadKleinB (t^2) (t^2/w.re)/
      Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
        (halfTurnQuadKleinA (t^2) (t^2/w.re))^2))=Real.pi*p/q) :
    let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)
    let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
      (zero_lt_one.trans (hu.trans_lt hut)))
    let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
    let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
    letI:=threeHalfTurn_native_group_discrete_of_original F G W hd
    let hConf:=threeHalfTurn_native_group_conformal F G W
    let P:=nativeConformalSubgroup_halfPlaneData H hConf
    ∃orders : List ℕ,HasCofiniteFuchsianSignature P.asFuchsianDisc 0 orders 0 ∧
      orders.length=3 ∧
      ∃N n : ℕ,0<N ∧ p≤N ∧ n∈orders ∧ q∣n ∧
        2*(N : ℝ)*(-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum)=1-2*(p : ℝ)/q ∧
        (∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity H
          (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon
            (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
              (one_lt_pow₀ (hu.trans_lt hut) (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
            (halfTurnQuadCanonical_finite _ _ _ _)).interior z=N) ∧ (3∈orders→3∣N) := by
  obtain ⟨orders,hSig,hlen,N,n,hN,hDegree,hnmem,hdiv,hArea,hCount⟩:=
    halfTurnCanonical_nonprimitive_signature_with_multiplicity
      u t hu hut w hw hn hc hd p q hp hpq hq hθ
  refine ⟨orders,hSig,hlen,N,n,hN,hDegree,hnmem,hdiv,hArea,hCount,?_⟩
  intro hThree
  let hu0:=zero_lt_one.trans_le hu
  let ht:=hu.trans_lt hut
  let ht0:=zero_lt_one.trans ht
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu0
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu0 ht0)
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
  let _originalDiscrete : DiscreteTopology H:=threeHalfTurn_native_group_discrete_of_original F G W hd
  let hConf:=threeHalfTurn_native_group_conformal F G W
  obtain ⟨z,hstab⟩:=halfTurn_actual_signature_three_point H hConf hSig hThree
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let geom:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_native_geometry Q hf
  let x:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
  let y:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F∈H:=Subgroup.subset_closure (by simp)
  have hG : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G∈H:=Subgroup.subset_closure (by simp)
  have hW : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W∈H:=Subgroup.subset_closure (by simp)
  let a : H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W,H.mul_mem (H.mul_mem hF hG) hW⟩
  have hprod : a.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F*G*W) := by
    apply IsometryEquiv.ext
    intro v
    change F•(G•(W•v))=(F*G*W)•v
    simp only [mul_smul]
  have horder : orderOf a=q := by
    calc
      orderOf a=orderOf a.val:=(orderOf_injective H.subtype Subtype.val_injective a).symm
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (F*G*W)):=by rw [hprod]
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F*G*W)):=hSLIsometry_orderOf_eq_realSLMobius _
      _=q:=hq.symm
  have hfix : a • x=x:=halfTurnCanonical_product_fixes_summit u t hu0 ht w hw hn hc
  have hLower : ∀g : H,g⁻¹ • z≠x :=
    halfTurn_cone_three_orbit_avoids_large_order_fixed H z x hstab a hfix
      (by rw [horder];omega)
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht0))
  have hD : D∈H := by
    rw [show D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht0)) from rfl,
      ←halfTurnNative_axis_product u t hu0 ht0]
    exact H.mul_mem hG hF
  let d : H:=⟨D,hD⟩
  have hmove : d • x=y:=halfTurnFour_summit_dilation (t^2) (t^2/w.re) hk hc w hw hn rfl
  have hUpper (g : H) : g⁻¹ • z≠y := by
    intro he
    apply hLower (g*d)
    rw [mul_inv_rev,mul_smul,he,←hmove,inv_smul_smul]
  have hR : IsCompact R.carrier:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf
  have hCarrier : _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity H R.carrier z=N :=
    (geom.angularMultiplicity_interior_eq hR H z).symm.trans (hCount z)
  have hDvd:=halfTurn_actual_angular_denominator_dvd H R.carrier hR z 4 N hCarrier
    (fun g=>halfTurnCanonical_quarter_angular_fraction (t^2) (t^2/w.re) hk hc
      (g⁻¹ • z) (hUpper g) (hLower g))
  rw [hstab] at hDvd
  exact (Nat.Coprime.dvd_mul_left (by decide : Nat.Coprime 3 4)).mp hDvd

end LowDimensionalTopology.Geometry.Fuchsian

set_option autoImplicit false
namespace LowDimensionalTopology.Geometry.Fuchsian

/-- Arithmetic only: the physical covering consumer must derive the equation. -/
theorem threeHalfTurn_two_three_degree_candidates (n N : ℕ) (hn : 7≤n)
    (hproduct : (n-6)*(N-3)=6) :
    (n=7 ∧ N=9) ∨ (n=8 ∧ N=6) ∨ (n=9 ∧ N=5) ∨ (n=12 ∧ N=4) := by
  have hdiv : n-6∣6:=⟨N-3,hproduct.symm⟩
  have hbound : n-6≤6:=Nat.le_of_dvd (by decide) hdiv
  have hupper : n≤12:=by omega
  interval_cases n <;> omega

/-- The exact source area equation and a degree at least three leave the
four integer candidates. No assertion of physical realization is made here. -/
theorem threeHalfTurn_two_three_area_candidates (n q N : ℕ)
    (hn : 7≤n) (hq : 5≤q) (hqn : q∣n) (hN : 3≤N)
    (harea : 2*(N:ℝ)*(1/6-1/(n:ℝ))=1-4/(q:ℝ)) :
    q=n ∧ ((n=7 ∧ N=9) ∨ (n=8 ∧ N=6) ∨ (n=9 ∧ N=5) ∨ (n=12 ∧ N=4)) := by
  have hnpos : (0:ℝ)<n:=by exact_mod_cast (by omega:0<n)
  have hqpos : (0:ℝ)<q:=by exact_mod_cast (by omega:0<q)
  have hdelta : (0:ℝ)<1/6-1/(n:ℝ):=by
    exact sub_pos.mpr (one_div_lt_one_div_of_lt (by norm_num) (by exact_mod_cast (by omega:6<n)))
  have hNR : (3:ℝ)≤N:=by exact_mod_cast hN
  have hrecip : (4:ℝ)/q≤6/n:=by
    have hnonneg:=mul_nonneg (sub_nonneg.mpr hNR) hdelta.le
    have hbound : (6:ℝ)*(1/6-1/(n:ℝ))≤1-4/(q:ℝ):=by
      nlinarith only [harea,hnonneg]
    have he : (6:ℝ)*(1/6-1/(n:ℝ))=1-6/(n:ℝ):=by ring
    rw [he] at hbound
    linarith only [hbound]
  have hsizeR : (2:ℝ)*n≤3*q:=by
    have hm:=(div_le_div_iff₀ hqpos hnpos).mp hrecip
    nlinarith only [hm]
  have hsize : 2*n≤3*q:=by exact_mod_cast hsizeR
  obtain ⟨k,hk⟩:=hqn
  have hkpos : 0<k:=by
    by_contra hh
    have hk0 : k=0:=by omega
    rw [hk0,mul_zero] at hk
    omega
  have hkone : k=1:=by
    by_contra hh
    have hk2 : 2≤k:=by omega
    have hmul:=Nat.mul_le_mul_left q hk2
    nlinarith [hk,hsize]
  have hqeq : q=n:=by simpa only [hkone,mul_one] using hk.symm
  subst q
  have heq : (N:ℝ)*((n:ℝ)-6)=3*((n:ℝ)-4):=by
    field_simp [ne_of_gt hnpos] at harea
    nlinarith only [harea]
  have hprodR : ((n-6:ℕ):ℝ)*((N-3:ℕ):ℝ)=6:=by
    rw [Nat.cast_sub (by omega:6≤n),Nat.cast_sub hN]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [heq]
  have hprod : (n-6)*(N-3)=6:=by exact_mod_cast hprodR
  exact ⟨rfl,threeHalfTurn_two_three_degree_candidates n N hn hprod⟩

/-- Divisibility of the actual degree by three is a separate geometric
obligation; once derived, only two of the four arithmetic pairs survive. -/
theorem threeHalfTurn_two_three_divisible_degree_candidates (n q N : ℕ)
    (hn : 7≤n) (hq : 5≤q) (hqn : q∣n) (hNpos : 0<N) (hdegree : 3∣N)
    (harea : 2*(N:ℝ)*(1/6-1/(n:ℝ))=1-4/(q:ℝ)) :
    q=n ∧ ((n=7 ∧ N=9) ∨ (n=8 ∧ N=6)) := by
  have hN : 3≤N:=Nat.le_of_dvd hNpos hdegree
  obtain ⟨heq,hcases⟩:=threeHalfTurn_two_three_area_candidates n q N hn hq hqn hN harea
  refine ⟨heq,?_⟩
  rcases hcases with h|h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨_,rfl⟩:=h
    norm_num at hdegree
  · obtain ⟨_,rfl⟩:=h
    norm_num at hdegree

end LowDimensionalTopology.Geometry.Fuchsian

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

/-- The source numerator-two, three-cone case has only its two remaining
actual angular covering candidates. The degree, area and cone data are all
constructed from the unchanged original canonical group. -/
theorem halfTurnCanonical_exceptional_cover_classification
    (u t : ℝ) (hu : 1≤u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
          (zero_lt_one.trans (hu.trans_lt hut)))),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set Mobius.complexMobiusGroup)))
    (p q : ℕ) (hp : 2≤p) (hpq : 2*p<q)
    (hq : q=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
        (zero_lt_one.trans (hu.trans_lt hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)))
    (hθ : Real.arccos (halfTurnQuadKleinB (t^2) (t^2/w.re)/
      Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
        (halfTurnQuadKleinA (t^2) (t^2/w.re))^2))=Real.pi*p/q) :
    let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)
    let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
      (zero_lt_one.trans (hu.trans_lt hut)))
    let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
    let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
    letI:=threeHalfTurn_native_group_discrete_of_original F G W hd
    let hConf:=threeHalfTurn_native_group_conformal F G W
    let P:=nativeConformalSubgroup_halfPlaneData H hConf
    ∃orders : List ℕ,HasCofiniteFuchsianSignature P.asFuchsianDisc 0 orders 0 ∧
      orders.length=3 ∧
      ∃N n : ℕ,0<N ∧ p≤N ∧ n∈orders ∧ q∣n ∧
        2*(N : ℝ)*(-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum)=1-2*(p : ℝ)/q ∧
        (∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity H
          (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon
            (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
              (one_lt_pow₀ (hu.trans_lt hut) (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
          (halfTurnQuadCanonical_finite _ _ _ _)).interior z=N) ∧ (3∈orders→3∣N) ∧ (p=2 → orders.Perm [2,3,n] → q=n ∧ ((n=7 ∧ N=9) ∨ (n=8 ∧ N=6))) := by
  obtain ⟨orders,hSig,hlen,N,n,hN,hDegree,hnmem,hdiv,hArea,hCount,hCone⟩:=
    halfTurnCanonical_nonprimitive_signature_cone_divisibility
      u t hu hut w hw hn hc hd p q hp hpq hq hθ
  refine ⟨orders,hSig,hlen,N,n,hN,hDegree,hnmem,hdiv,hArea,hCount,hCone,?_⟩
  intro hp2 hPerm
  have hThree : 3∈orders:=hPerm.mem_iff.mpr (by simp)
  have hn2:=hSig.orders_two_le hnmem
  have hqn : q≤n:=Nat.le_of_dvd (by omega) hdiv
  have hClass:=halfTurn_nonprimitive_order_list_classification orders
    (fun _ hm=>hSig.orders_two_le hm) hlen p q N n hp hpq hDegree hnmem hqn hArea
  have hn7 : 7≤n := by
    rcases hClass with ⟨_,_,hn7⟩|⟨hp3,_,_⟩|⟨_,h24,hn5⟩
    · exact hn7
    · omega
    · have hh:=h24.mem_iff.mp hThree
      norm_num at hh
      omega
  have hsum : (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum=
      3-(1/(2 : ℝ)+1/(3 : ℝ)+1/(n : ℝ)) := by
    rw [(hPerm.map (fun m : ℕ=>1-1/(m : ℝ))).sum_eq]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring
  have hScalar : 2*(N : ℝ)*(1/6-1/(n : ℝ))=1-4/(q : ℝ) := by
    rw [hsum,hp2] at hArea
    norm_num only [Nat.cast_ofNat] at hArea
    linear_combination hArea
  exact threeHalfTurn_two_three_divisible_degree_candidates n q N hn7 (by omega)
    hdiv hN (hCone hThree) hScalar

end LowDimensionalTopology.Geometry.Fuchsian
