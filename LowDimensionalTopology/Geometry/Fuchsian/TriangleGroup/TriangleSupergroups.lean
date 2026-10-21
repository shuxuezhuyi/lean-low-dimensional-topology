/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSignatureCharacterization
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.OriginalQuotientArea
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaActualSignature
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalActualSignatureArea
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleFirstKind
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.FiniteIndexConjugacy
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FirstKindShortSignatures
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FirstKindFiniteArea
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.LowGenusSignatureArea
/-!
# Discrete overgroups of triangle groups

Finite-area subgroup selectors give finite index and an exact area formula for the ambient
Fuchsian group. These formulas, together with inherited elliptic orders and cusp counts, show
that a discrete overgroup of a geometric triangle group is again a geometric triangle group.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint Pointwise ENNReal
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
local instance triangleSupergroupSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel Mobius.ExtendedComplex
local instance triangleSupergroupSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- A true finite-area subgroup selector forces actual finite index and finite original quotient area for the entire ambient Fuchsian group. -/
theorem fuchsian_finite_area_subgroup_index
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (K : Subgroup H) (F : Set P.domain.carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet K P.domain.carrier F)
    (hm : NullMeasurableSet F P.area)
    (ha : P.area F ≠ ⊤) :
    K.FiniteIndex ∧ fuchsianQuotientAreaMeasure P univ ≠ ⊤ := by
  let _triangleSupergroupCountable : Countable H := P.countable
  have hsel := fuchsianAreaSelector_spec P
  have hA := fuchsianFundamentalSet_subgroup_index_area P K hF hm hsel.1 hsel.2
  have hzero : P.area (fuchsianAreaSelector P) ≠ 0 :=
    (hsel.1.measureFundamentalDomain hsel.2).measure_ne_zero (fuchsian_original_area_ne_zero P)
  have hcard : (ENat.card (H ⧸ K) : ℝ≥0∞) ≠ ⊤ := by
    intro he
    rw [he, ENNReal.top_mul hzero] at hA
    exact ha hA
  have hcard' : ENat.card (H ⧸ K) ≠ ⊤ := by
    exact fun he => hcard (by rw [he, ENat.toENNReal_top])
  let _triangleSupergroupFiniteQuotient : Finite (H ⧸ K) :=
    ENat.card_lt_top.mp (lt_top_iff_ne_top.mpr hcard')
  have hk : K.FiniteIndex := K.finiteIndex_of_finite_quotient
  have hn : (ENat.card (H ⧸ K) : ℝ≥0∞) ≠ 0 := by
    rw [ENat.card_eq_coe_natCard, ENat.toENNReal_coe]
    exact_mod_cast (Nat.card_pos (α := H ⧸ K)).ne'
  refine ⟨hk, ?_⟩
  rw [←fuchsianFundamentalSet_quotient_area P _ hsel.1 hsel.2]
  intro he
  rw [he, ENNReal.mul_top hn] at hA
  exact ha hA

/-- Finite generation of the entire overgroup follows from its derived actual finite-area Dirichlet domain. -/
theorem fuchsian_finite_area_overgroup_finitelyGenerated
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (K : Subgroup H) (F : Set P.domain.carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet K P.domain.carrier F)
    (hm : NullMeasurableSet F P.area)
    (ha : P.area F ≠ ⊤) : H.FG := by
  obtain ⟨_hk, hA⟩ := fuchsian_finite_area_subgroup_index P K F hF hm ha
  obtain ⟨w, hw, _hgood⟩ := exists_actual_dirichlet_horocycle_good_center P
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  apply finite_area_polygon_group_finitelyGenerated hD
  rwa [fuchsianFundamentalDomain_quotient_area P _ hD.locallyFinite.fundamental]

/-- The area/index estimate leaves only three or four genuine marked points once an equality case really forces a parabolic element in the overgroup. -/
theorem triangle_supergroup_signature_three_or_four (s : FuchsianSignature)
    (hb : s.boundaryHyperbolicEnds = 0) (k : ℕ) (hk : 2 ≤ k)
    (hpos : 0 < s.deficit) (hbudget : (k : ℝ) * s.deficit ≤ 1)
    (heqpar : (k : ℝ) * s.deficit = 1 → 0 < s.parabolicEnds) :
    s.genus = 0 ∧ 3 ≤ s.ellipticOrders.length + s.parabolicEnds ∧
      s.ellipticOrders.length + s.parabolicEnds ≤ 4 := by
  have hL := signature_elliptic_sum_lower s.ellipticOrders s.ellipticOrders_two_le
  have hn : (0 : ℝ) ≤ s.ellipticOrders.length := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ s.parabolicEnds := Nat.cast_nonneg _
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hhalf : s.deficit ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hkR hpos.le
    linarith
  have hdef : s.deficit = 2 * (s.genus : ℝ) - 2 + s.parabolicEnds +
      (s.ellipticOrders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum := by
    simp [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hb]
  have hg1 : s.genus ≤ 1 := by
    by_contra h
    have hg : (2 : ℝ) ≤ s.genus := by exact_mod_cast (show 2 ≤ s.genus by omega)
    linarith
  have hg : s.genus = 0 := by
    by_contra h
    have hgone : s.genus = 1 := by omega
    have hpzero : s.parabolicEnds = 0 := by
      by_contra hpne
      have hpone : (1 : ℝ) ≤ s.parabolicEnds := by
        exact_mod_cast (show 1 ≤ s.parabolicEnds by omega)
      simp only [hgone, Nat.cast_one] at hdef
      linarith
    have hnonempty : s.ellipticOrders ≠ [] := by
      intro he
      simp only [hgone, hpzero, he, Nat.cast_one, Nat.cast_zero,
        List.map_nil, List.sum_nil] at hdef
      linarith
    have hlen : (1 : ℝ) ≤ s.ellipticOrders.length := by
      have hne : s.ellipticOrders.length ≠ 0 := fun h =>
        hnonempty (List.length_eq_zero_iff.mp h)
      exact_mod_cast (show 1 ≤ s.ellipticOrders.length by omega)
    have hlow : 1 / 2 ≤ s.deficit := by
      simp only [hgone, hpzero, Nat.cast_one, Nat.cast_zero] at hdef
      linarith
    have heq : (k : ℝ) * s.deficit = 1 := by
      have h := mul_le_mul_of_nonneg_right hkR hpos.le
      apply le_antisymm hbudget
      linarith
    have hp' := heqpar heq
    omega
  have hdef0 : s.deficit = -2 + s.parabolicEnds +
      (s.ellipticOrders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum := by
    simpa only [hg, Nat.cast_zero, mul_zero, zero_sub] using hdef
  have hU : (s.ellipticOrders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum ≤
      (s.ellipticOrders.length : ℝ) := by
    by_cases he : s.ellipticOrders = []
    · simp [he]
    · exact (signature_elliptic_sum_lt_length _ s.ellipticOrders_two_le he).le
  have hthree : 3 ≤ s.ellipticOrders.length + s.parabolicEnds := by
    have h : (2 : ℝ) < (s.ellipticOrders.length : ℝ) + s.parabolicEnds := by linarith
    have h' : 2 < s.ellipticOrders.length + s.parabolicEnds := by exact_mod_cast h
    omega
  have hfive : s.ellipticOrders.length + s.parabolicEnds ≤ 5 := by
    have h : (s.ellipticOrders.length : ℝ) + s.parabolicEnds ≤ 5 := by linarith
    exact_mod_cast h
  have hnotfive : s.ellipticOrders.length + s.parabolicEnds ≠ 5 := by
    intro he
    have heR : (s.ellipticOrders.length : ℝ) + s.parabolicEnds = 5 := by exact_mod_cast he
    have hlow : 1 / 2 ≤ s.deficit := by linarith
    have heq : (k : ℝ) * s.deficit = 1 := by
      have h := mul_le_mul_of_nonneg_right hkR hpos.le
      apply le_antisymm hbudget
      linarith
    have hpone : (1 : ℝ) ≤ s.parabolicEnds := by exact_mod_cast heqpar heq
    linarith
  exact ⟨hg, hthree, by omega⟩

/-- A four-point signature with finite orders cannot satisfy the proper-overgroup area identity when its maximum order bounds the original three orders. -/
theorem triangle_supergroup_four_finite_impossible (l : List ℕ)
    (hl : ∀ n ∈ l, 2 ≤ n) (hlen : l.length = 4) (m p q r k : ℕ)
    (hm : m ∈ l) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hpm : p ≤ m) (hqm : q ≤ m) (hrm : r ≤ m) (hk : 2 ≤ k)
    (hpos : 0 < -2 + (l.map (fun n : ℕ => 1 - 1 / (n : ℝ))).sum)
    (hA : (k : ℝ) * (-2 + (l.map (fun n : ℕ => 1 - 1 / (n : ℝ))).sum) =
      1 - 1 / (p : ℝ) - 1 / (q : ℝ) - 1 / (r : ℝ)) : False := by
  have htail := signature_elliptic_sum_lower (l.erase m)
    (fun n hn => hl n (List.mem_of_mem_erase hn))
  have hlength : (l.erase m).length = 3 := by
    rw [List.length_erase_of_mem hm, hlen]
  rw [hlength] at htail
  have hsum := signature_elliptic_sum_perm (List.perm_cons_erase hm)
  simp only [List.map_cons, List.sum_cons] at hsum
  have hp' := signature_reciprocal_le p m (by omega) hpm
  have hq' := signature_reciprocal_le q m (by omega) hqm
  have hr' := signature_reciprocal_le r m (by omega) hrm
  have hmpos : 0 < 1 / (m : ℝ) := one_div_pos.mpr (by exact_mod_cast (show 0 < m by have h:=hl m hm;omega))
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h := mul_le_mul_of_nonneg_right hkR hpos.le
  norm_num at htail
  simp only [one_div] at hA hpos hsum hp' hq' hr' hmpos h htail
  linarith

/-- Every genuine elliptic order of a subgroup is bounded by a genuine elliptic order of the original overgroup, through actual point-stabilizer inclusion. -/
theorem fuchsian_subgroup_elliptic_order_le
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup Mobius.complexMobiusGroup) (hKH : K ≤ H)
    (c : FuchsianCyclicConjugacyClasses (fuchsianDiscRestrict D K hKH) .elliptic) :
    ∃ d : FuchsianCyclicConjugacyClasses D .elliptic,
      fuchsianEllipticClassOrder (fuchsianDiscRestrict D K hKH) c ≤
        fuchsianEllipticClassOrder D d := by
  induction c using Quotient.inductionOn with
  | _ L =>
    obtain ⟨hL, f, hfL, hf⟩ := L.property
    have hfH : f ∈ H := hKH (hL.1 hfL)
    obtain ⟨p, hp, _hu⟩ := elliptic_disc_existsUnique_fixed f hf D.isDisc
      (D.image_eq ⟨f, hfH⟩)
    let M : fuchsianMaximalCyclicSubgroups H .elliptic :=
      ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val,
        elliptic_stabilizer_isMaximalCyclic D f hfH hf p hp,
        f, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val f).mpr ⟨hfH, hp⟩, hf⟩
    have hLM : L.val ≤ M.val := by
      intro g hg
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val g).mpr
        ⟨hKH (hL.1 hg), cyclic_elliptic_disc_fixes D L.val (hL.1.trans hKH)
          hL.2.1 f hfL hf p hp g hg⟩
    let _triangleSupergroupEllipticFinite : Finite M.val := fuchsianMaximalElliptic_finite D M
    refine ⟨Quotient.mk _ M, ?_⟩
    change Nat.card L.val ≤ Nat.card M.val
    exact Nat.card_le_card_of_injective (Subgroup.inclusion hLM) (Subgroup.inclusion_injective hLM)

/-- Equality in the triangular area bound forces precisely three genuine cusp entries and no elliptic entries. -/
theorem triangle_signature_deficit_one (s : FuchsianSignature) (hg : s.genus = 0)
    (hb : s.boundaryHyperbolicEnds = 0) (hn : s.ellipticOrders.length + s.parabolicEnds = 3)
    (hd : s.deficit = 1) : s.ellipticOrders = [] ∧ s.parabolicEnds = 3 := by
  have hN : (s.ellipticOrders.length : ℝ) + s.parabolicEnds = 3 := by exact_mod_cast hn
  have hD : -2 + (s.parabolicEnds : ℝ) +
      (s.ellipticOrders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum = 1 := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hg, hb, Nat.cast_zero,
      mul_zero, zero_sub, add_zero] using hd
  have he : s.ellipticOrders = [] := by
    by_contra hne
    have h := signature_elliptic_sum_lt_length _ s.ellipticOrders_two_le hne
    linarith
  exact ⟨he, by simpa only [he, List.length_nil, zero_add] using hn⟩

/-- A remaining four-point signature with a genuine cusp forces index two, one cusp and equality in the original triangular area bound. -/
theorem triangle_supergroup_four_with_cusp (s : FuchsianSignature)
    (hg : s.genus = 0) (hb : s.boundaryHyperbolicEnds = 0)
    (hn : s.ellipticOrders.length + s.parabolicEnds = 4) (hp : 0 < s.parabolicEnds)
    (k : ℕ) (hk : 2 ≤ k) (hbudget : (k : ℝ) * s.deficit ≤ 1) :
    k = 2 ∧ s.parabolicEnds = 1 ∧ (k : ℝ) * s.deficit = 1 := by
  have hL := signature_elliptic_sum_lower s.ellipticOrders s.ellipticOrders_two_le
  have hN : (s.ellipticOrders.length : ℝ) + s.parabolicEnds = 4 := by exact_mod_cast hn
  have hP : (1 : ℝ) ≤ s.parabolicEnds := by exact_mod_cast hp
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : s.deficit = -2 + (s.parabolicEnds : ℝ) +
      (s.ellipticOrders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum := by
    simp [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hg, hb]
  have hlow : 1 / 2 ≤ s.deficit := by linarith
  have hhalf : s.deficit ≤ 1 / 2 := by nlinarith
  have hkR : (k : ℝ) = 2 := by nlinarith
  have hpR : (s.parabolicEnds : ℝ) = 1 := by linarith
  refine ⟨by exact_mod_cast hkR, by exact_mod_cast hpR, ?_⟩
  nlinarith

/-- The actual same unit disc with the restricted original subgroup action. -/
theorem unitDiscSubgroupData
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H) : UnitDiscFuchsianGroup K where
  invariant := (fuchsianDiscRestrict P.asFuchsianDisc K hKH).invariant
  discontinuous := (fuchsianDiscRestrict P.asFuchsianDisc K hKH).discontinuous

/-- A first-kind finitely generated actual subgroup forces finite index and finite generation of the whole original Fuchsian overgroup. -/
theorem fuchsian_firstKind_finitelyGenerated_subgroup_index
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H)
    (hfirst : (unitDiscSubgroupData P K hKH).asFuchsianDisc.IsFirstKind) (hFG : K.FG) :
    (K.subgroupOf H).FiniteIndex ∧ H.FG := by
  let Q := unitDiscSubgroupData P K hKH
  let _triangleSupergroupRestrictedAction : MulAction K P.domain.carrier :=
    inferInstanceAs (MulAction K Q.domain.carrier)
  obtain ⟨w, hw, _hgood⟩ := exists_actual_dirichlet_horocycle_good_center Q
  have hD := dirichletDomain_fundamental Q w hw
  have ha := firstKind_finitelyGenerated_area_ne_top Q hfirst hFG hD
  obtain ⟨F, hF, hDF, hFC⟩ := hD.exists_fundamentalSet
  have hm := hD.nullMeasurableSet_between hDF hFC
  have haF : P.area F ≠ ⊤ := by
    change Q.area F ≠ ⊤
    rwa [←hD.area_between hDF hFC]
  let e : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  let E := orbitQuotientEquivOfMulEquiv (X := P.domain.carrier) e (by intro g x; rfl)
  have he (x y : P.domain.carrier) :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (K.subgroupOf H) P.domain.carrier x =
          _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (K.subgroupOf H) P.domain.carrier y ↔
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Q.domain.carrier x = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Q.domain.carrier y := by
    exact E.injective.eq_iff.symm
  have hF' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet (K.subgroupOf H) P.domain.carrier F := by
    intro x
    obtain ⟨y, hy, hu⟩ := hF x
    exact ⟨y, ⟨hy.1, (he y x).mpr hy.2⟩,
      fun z hz => hu z ⟨hz.1, (he z x).mp hz.2⟩⟩
  exact ⟨(fuchsian_finite_area_subgroup_index P _ F hF' hm haF).1,
    fuchsian_finite_area_overgroup_finitelyGenerated P _ F hF' hm haF⟩

/-- A first-kind subgroup fills the same actual invariant boundary for its whole overgroup. -/
theorem fuchsian_firstKind_of_subgroup {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H)
    (hfirst : (unitDiscSubgroupData P K hKH).asFuchsianDisc.IsFirstKind) :
    P.asFuchsianDisc.IsFirstKind := by
  apply Set.Subset.antisymm P.asFuchsianDisc.limitSet_subset_frontier
  change frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ⊆ fuchsianLimitSet H
  have hfirst' : fuchsianLimitSet K = frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := hfirst
  rw [←hfirst']
  apply closure_mono
  rintro z ⟨f, hf, hfix⟩
  exact ⟨⟨f.val, hKH f.property⟩, hf, hfix⟩

/-- An actual finite-area domain supplies its own genuine whole-group signature and matching exact area expression with the same completion genus. -/
theorem finite_area_unitDisc_signature_area
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier)
    (hD : IsFuchsianFundamentalDomain P D) (ha : P.area D ≠ ⊤) :
    ∃ s : FuchsianSignature, s.boundaryHyperbolicEnds = 0 ∧
      HasCofiniteFuchsianSignature P.asFuchsianDisc s.genus s.ellipticOrders s.parabolicEnds ∧
      (P.area D).toReal = 2 * Real.pi * s.deficit := by
  have hD' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier (geometricModelArea P.asFuchsianDisc) D := by
    rw [geometricModelArea_asUnitDisc]
    exact hD
  have ha' : geometricModelArea P.asFuchsianDisc D ≠ ⊤ := by
    rwa [geometricModelArea_asUnitDisc]
  let _triangleSupergroupActualEllipticFinite : Finite
      (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic) :=
    finite_area_elliptic_classes_finite P.asFuchsianDisc D hD' ha'
  obtain ⟨g, hg, hA⟩ := finite_area_original_actual_signature_area P.asFuchsianDisc D hD' ha'
  let s : FuchsianSignature :=
    ⟨g, fuchsianEllipticOrderList P.asFuchsianDisc,
      fuchsianEllipticOrderList_two_le P.asFuchsianDisc,
      Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic), 0⟩
  refine ⟨s, rfl, ?_, ?_⟩
  · exact { ellipticClassesFinite := inferInstance
            parabolicClassesFinite := finite_area_parabolic_classes_finite P.asFuchsianDisc D hD' ha'
            compact := _root_.LowDimensionalTopology.Geometry.Surfaces.HandleSeparation.hasTopologicalGenus_compactSpace hg
            topologicalGenus := hg
            ellipticOrders := List.Perm.refl _
            cuspCount := rfl }
  · rw [geometricModelArea_asUnitDisc] at hA
    simp only [s, _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, Nat.cast_zero, add_zero]
    linear_combination hA

/-- The actual open subgroup and overgroup fundamental domains obey the exact finite-index area formula, with the index and ambient finiteness derived from subgroup area. -/
theorem fuchsian_subgroup_fundamentalDomain_index_area
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H)
    (D₀ : Set (unitDiscSubgroupData P K hKH).domain.carrier) (D₁ : Set P.domain.carrier)
    (hD₀ : IsFuchsianFundamentalDomain (unitDiscSubgroupData P K hKH) D₀)
    (hD₁ : IsFuchsianFundamentalDomain P D₁)
    (ha : (unitDiscSubgroupData P K hKH).area D₀ ≠ ⊤) :
    (K.subgroupOf H).FiniteIndex ∧
      (unitDiscSubgroupData P K hKH).area D₀ =
        ((K.subgroupOf H).index : ℝ≥0∞) * P.area D₁ ∧ P.area D₁ ≠ ⊤ := by
  let Q := unitDiscSubgroupData P K hKH
  let _triangleIndexAreaRestrictedAction : MulAction K P.domain.carrier :=
    inferInstanceAs (MulAction K Q.domain.carrier)
  obtain ⟨F₀, hF₀, hDF₀, hFC₀⟩ := hD₀.exists_fundamentalSet
  obtain ⟨F₁, hF₁, hDF₁, hFC₁⟩ := hD₁.exists_fundamentalSet
  have hm₀ := hD₀.nullMeasurableSet_between hDF₀ hFC₀
  have hm₁ := hD₁.nullMeasurableSet_between hDF₁ hFC₁
  have he₀ : P.area D₀ = P.area F₀ := hD₀.area_between hDF₀ hFC₀
  have he₁ := hD₁.area_between hDF₁ hFC₁
  have haF : P.area F₀ ≠ ⊤ := by rwa [←he₀]
  let e : K.subgroupOf H ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  let E := orbitQuotientEquivOfMulEquiv (X := P.domain.carrier) e (by intro g x; rfl)
  have he (x y : P.domain.carrier) :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (K.subgroupOf H) P.domain.carrier x =
          _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (K.subgroupOf H) P.domain.carrier y ↔
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Q.domain.carrier x = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Q.domain.carrier y :=
    E.injective.eq_iff.symm
  have hF₀' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet (K.subgroupOf H) P.domain.carrier F₀ := by
    intro x
    obtain ⟨y, hy, hu⟩ := hF₀ x
    exact ⟨y, ⟨hy.1, (he y x).mpr hy.2⟩,
      fun z hz => hu z ⟨hz.1, (he z x).mp hz.2⟩⟩
  obtain ⟨hk, hQ⟩ := fuchsian_finite_area_subgroup_index P _ F₀ hF₀' hm₀ haF
  let _triangleIndexAreaFiniteIndex : (K.subgroupOf H).FiniteIndex := hk
  have hA := fuchsianFundamentalSet_finite_index_area P (K.subgroupOf H) hF₀' hm₀ hF₁ hm₁
  rw [←he₀, ←he₁] at hA
  refine ⟨hk, hA, ?_⟩
  rwa [fuchsianFundamentalDomain_quotient_area P _ hD₁]

/-- Every actual elliptic order of the subgroup is bounded by a listed actual elliptic order of the overgroup signature. -/
theorem cofinite_subgroup_signature_elliptic_order_bound
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup Mobius.complexMobiusGroup) (hKH : K ≤ H)
    {g₀ p₀ g₁ p₁ : ℕ} {orders₀ orders₁ : List ℕ}
    (h₀ : HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) g₀ orders₀ p₀)
    (h₁ : HasCofiniteFuchsianSignature D g₁ orders₁ p₁) (m : ℕ) (hm : m ∈ orders₀) :
    ∃ n ∈ orders₁, m ≤ n := by
  obtain ⟨c, hc⟩ := h₀.mem_orders.mp hm
  obtain ⟨d, hd⟩ := fuchsian_subgroup_elliptic_order_le D K hKH c
  exact ⟨fuchsianEllipticClassOrder D d, h₁.mem_orders.mpr ⟨d, rfl⟩, by rwa [hc] at hd⟩

/-- A genuine parabolic class of the subgroup forces an actual cusp class of the overgroup, without a finite-index assumption. -/
theorem cofinite_subgroup_signature_cusp_pos
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup Mobius.complexMobiusGroup) (hKH : K ≤ H)
    {g₀ p₀ g₁ p₁ : ℕ} {orders₀ orders₁ : List ℕ}
    (h₀ : HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) g₀ orders₀ p₀)
    (h₁ : HasCofiniteFuchsianSignature D g₁ orders₁ p₁) (hp₀ : 0 < p₀) : 0 < p₁ := by
  have hcard : 0 < Nat.card (FuchsianCyclicConjugacyClasses
      (fuchsianDiscRestrict D K hKH) .parabolic) := by rwa [←h₀.cuspCount]
  obtain ⟨c⟩ := (Nat.card_pos_iff.mp hcard).1
  obtain ⟨f, hf, hft⟩ := c.out.property.2
  have hfH : f ∈ H := hKH (c.out.property.1.1 hf)
  by_contra hnot
  have hp₁ : p₁ = 0 := by omega
  have hcard₁ : Nat.card (FuchsianCyclicConjugacyClasses D .parabolic) = 0 := by
    rw [←h₁.cuspCount, hp₁]
  have hEmpty : IsEmpty (FuchsianCyclicConjugacyClasses D .parabolic) :=
    (Nat.card_eq_zero.mp hcard₁).resolve_right h₁.parabolicClassesFinite.not_infinite
  exact (fuchsianCyclicConjugacyClasses_isEmpty_iff D .parabolic).mp hEmpty f hfH hft

/-- Exact area and the genuine inherited order and cusp counts exclude every nontriangular overgroup signature. -/
theorem triangle_supergroup_signature_classification (s₀ s : FuchsianSignature)
    (hg₀ : s₀.genus = 0) (hb₀ : s₀.boundaryHyperbolicEnds = 0)
    (hn₀ : s₀.ellipticOrders.length + s₀.parabolicEnds = 3)
    (hb : s.boundaryHyperbolicEnds = 0) (k : ℕ) (hk : 2 ≤ k)
    (hpos : 0 < s.deficit) (hA : (k : ℝ) * s.deficit = s₀.deficit)
    (horders : ∀ m ∈ s₀.ellipticOrders, ∃ n ∈ s.ellipticOrders, m ≤ n)
    (hcusp : 0 < s₀.parabolicEnds → 0 < s.parabolicEnds)
    (hcount : s₀.parabolicEnds ≤ k * s.parabolicEnds) :
    s.genus = 0 ∧ s.ellipticOrders.length + s.parabolicEnds = 3 := by
  classical
  have hU₀ : (s₀.ellipticOrders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum ≤
      (s₀.ellipticOrders.length : ℝ) := by
    by_cases he : s₀.ellipticOrders = []
    · simp [he]
    · exact (signature_elliptic_sum_lt_length _ s₀.ellipticOrders_two_le he).le
  have hN₀ : (s₀.ellipticOrders.length : ℝ) + s₀.parabolicEnds = 3 := by exact_mod_cast hn₀
  have hbudget : (k : ℝ) * s.deficit ≤ 1 := by
    rw [hA]
    simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hg₀, hb₀, Nat.cast_zero,
      mul_zero, zero_sub, add_zero]
    linarith
  have heqpar : (k : ℝ) * s.deficit = 1 → 0 < s.parabolicEnds := by
    intro he
    have hzero := triangle_signature_deficit_one s₀ hg₀ hb₀ hn₀ (hA.symm.trans he)
    apply hcusp
    rw [hzero.2]
    decide
  obtain ⟨hg, hthree, hfour⟩ :=
    triangle_supergroup_signature_three_or_four s hb k hk hpos hbudget heqpar
  refine ⟨hg, ?_⟩
  by_contra hn
  have hn₄ : s.ellipticOrders.length + s.parabolicEnds = 4 := by omega
  by_cases hp : 0 < s.parabolicEnds
  · obtain ⟨hk₂, hp₁, heq⟩ := triangle_supergroup_four_with_cusp s hg hb hn₄ hp k hk hbudget
    have hp₀ := (triangle_signature_deficit_one s₀ hg₀ hb₀ hn₀ (hA.symm.trans heq)).2
    rw [hp₀, hk₂, hp₁] at hcount
    omega
  · have hpzero : s.parabolicEnds = 0 := by omega
    have hp₀ : s₀.parabolicEnds = 0 := by
      by_contra hne
      have h := hcusp (by omega)
      omega
    have hlen : s.ellipticOrders.length = 4 := by omega
    have hlen₀ : s₀.ellipticOrders.length = 3 := by omega
    obtain ⟨p, q, r, he₀⟩ := List.length_eq_three.mp hlen₀
    have hp₂ := s₀.ellipticOrders_two_le p (by rw [he₀]; simp)
    have hq₂ := s₀.ellipticOrders_two_le q (by rw [he₀]; simp)
    have hr₂ := s₀.ellipticOrders_two_le r (by rw [he₀]; simp)
    have hnonempty : s.ellipticOrders.toFinset.Nonempty := by
      obtain ⟨a, as, he⟩ := List.exists_cons_of_ne_nil
        (show s.ellipticOrders ≠ [] by intro he; rw [he] at hlen; simp at hlen)
      exact ⟨a, List.mem_toFinset.mpr (by rw [he]; simp)⟩
    let m := s.ellipticOrders.toFinset.max' hnonempty
    have hm : m ∈ s.ellipticOrders := List.mem_toFinset.mp (Finset.max'_mem _ hnonempty)
    have hmax : ∀ a ∈ s₀.ellipticOrders, a ≤ m := by
      intro a ha
      obtain ⟨b, hb', hab⟩ := horders a ha
      exact hab.trans (Finset.le_max' _ _ (List.mem_toFinset.mpr hb'))
    have hpm := hmax p (by rw [he₀]; simp)
    have hqm := hmax q (by rw [he₀]; simp)
    have hrm := hmax r (by rw [he₀]; simp)
    have hD : s.deficit = -2 +
        (s.ellipticOrders.map (fun n : ℕ => 1 - 1 / (n : ℝ))).sum := by
      simp [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hg, hb, hpzero]
    apply triangle_supergroup_four_finite_impossible s.ellipticOrders s.ellipticOrders_two_le
      hlen m p q r k hm hp₂ hq₂ hr₂ hpm hqm hrm hk (by rwa [←hD])
    rw [←hD, hA]
    simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, hg₀, hb₀, hp₀, he₀,
      Nat.cast_zero, mul_zero, zero_sub, add_zero, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    ring

/-- An actual first-kind, finitely generated three-marked subgroup forces the overgroup itself to have a genuine genus-zero three-marked signature. -/
theorem fuchsian_three_marked_subgroup_signature
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H)
    (hfirst : (unitDiscSubgroupData P K hKH).asFuchsianDisc.IsFirstKind) (hFG : K.FG)
    (orders₀ : List ℕ) (cusps₀ : ℕ)
    (hSig₀ : HasCofiniteFuchsianSignature (unitDiscSubgroupData P K hKH).asFuchsianDisc
      0 orders₀ cusps₀) (hthree₀ : orders₀.length + cusps₀ = 3) :
    ∃ orders : List ℕ, ∃ cusps : ℕ,
      HasCofiniteFuchsianSignature P.asFuchsianDisc 0 orders cusps ∧
        orders.length + cusps = 3 := by
  classical
  let _triangleThreeMarkedOvergroupCountable : Countable H := P.countable
  by_cases hEq : K = H
  · subst K
    exact ⟨orders₀, cusps₀, hSig₀, hthree₀⟩
  let Q := unitDiscSubgroupData P K hKH
  obtain ⟨w₀, hw₀, _hgood₀⟩ := exists_actual_dirichlet_horocycle_good_center Q
  obtain ⟨w₁, hw₁, _hgood₁⟩ := exists_actual_dirichlet_horocycle_good_center P
  let D₀ := dirichletDomain Q w₀
  let D₁ := dirichletDomain P w₁
  have hD₀ := dirichletDomain_fundamental Q w₀ hw₀
  have hD₁ := dirichletDomain_fundamental P w₁ hw₁
  have ha₀ := firstKind_finitelyGenerated_area_ne_top Q hfirst hFG hD₀
  obtain ⟨hindex, hAindex, ha₁⟩ :=
    fuchsian_subgroup_fundamentalDomain_index_area P K hKH D₀ D₁ hD₀ hD₁ ha₀
  let _triangleSignatureOvergroupFiniteIndex : (K.subgroupOf H).FiniteIndex := hindex
  have hk : 2 ≤ (K.subgroupOf H).index := by
    have hne : K.subgroupOf H ≠ ⊤ := fun he => hEq
      (le_antisymm hKH (Subgroup.subgroupOf_eq_top.mp he))
    exact (K.subgroupOf H).one_lt_index_of_ne_top hne
  obtain ⟨s, hsB, hs, hA⟩ := finite_area_unitDisc_signature_area P D₁ hD₁ ha₁
  have hD₀' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain K
      (fuchsianGeometricDomain Q.asFuchsianDisc).carrier (geometricModelArea Q.asFuchsianDisc) D₀ := by
    rw [geometricModelArea_asUnitDisc]
    exact hD₀
  have ha₀' : geometricModelArea Q.asFuchsianDisc D₀ ≠ ⊤ := by
    rwa [geometricModelArea_asUnitDisc]
  have hA₀ := cofinite_signature_area_of_genus_le_one Q.asFuchsianDisc D₀ hD₀' ha₀'
    0 cusps₀ orders₀ hSig₀ (by decide)
  rw [geometricModelArea_asUnitDisc] at hA₀
  let s₀ : FuchsianSignature := ⟨0, orders₀, fun _ hm => hSig₀.orders_two_le hm, cusps₀, 0⟩
  have hA₀' : (Q.area D₀).toReal = 2 * Real.pi * s₀.deficit := by
    simp only [s₀, _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, Nat.cast_zero, add_zero]
    linear_combination hA₀
  have hAindexR := congrArg ENNReal.toReal hAindex
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, hA₀', hA] at hAindexR
  have hdef : ((K.subgroupOf H).index : ℝ) * s.deficit = s₀.deficit := by
    apply mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity)
    linear_combination -hAindexR
  obtain ⟨F, hF, hDF, hFC⟩ := hD₁.exists_fundamentalSet
  have hF' : IsFuchsianFundamentalSet P F := hF
  have hneF : P.area F ≠ 0 :=
    (hF'.measureFundamentalDomain (hD₁.nullMeasurableSet_between hDF hFC)).measure_ne_zero
      (fuchsian_original_area_ne_zero P)
  have hneD₁ : P.area D₁ ≠ 0 := by rwa [hD₁.area_between hDF hFC]
  have hpos : 0 < s.deficit := by
    have h := ENNReal.toReal_pos hneD₁ ha₁
    rw [hA] at h
    exact (mul_pos_iff_of_pos_left (show 0 < 2 * Real.pi by positivity)).mp h
  have hSig₀' : HasCofiniteFuchsianSignature
      (fuchsianDiscRestrict P.asFuchsianDisc K hKH) 0 orders₀ cusps₀ := hSig₀
  have horders : ∀ m ∈ s₀.ellipticOrders, ∃ n ∈ s.ellipticOrders, m ≤ n :=
    cofinite_subgroup_signature_elliptic_order_bound P.asFuchsianDisc K hKH hSig₀' hs
  have hcusp : 0 < s₀.parabolicEnds → 0 < s.parabolicEnds :=
    cofinite_subgroup_signature_cusp_pos P.asFuchsianDisc K hKH hSig₀' hs
  let _triangleSignatureOvergroupParabolicFinite : Finite
      (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) := hs.parabolicClassesFinite
  have hcount := fuchsian_parabolic_conjugacy_card_le_index_mul P.asFuchsianDisc K hKH
  rw [←hSig₀'.cuspCount, ←hs.cuspCount] at hcount
  obtain ⟨hg, hthree⟩ := triangle_supergroup_signature_classification s₀ s rfl rfl hthree₀ hsB
    (K.subgroupOf H).index hk hpos hdef horders hcusp hcount
  exact ⟨s.ellipticOrders, s.parabolicEnds, by simpa only [hg] using hs, hthree⟩


/-- A discrete original unit-disc group containing a genuine geometric triangle group is itself a geometric triangle group. -/
theorem unitDisc_triangle_overgroup_isMobiusTriangleGroup
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H)
    (hTri : IsMobiusTriangleGroup K) : IsMobiusTriangleGroup H := by
  let Q := unitDiscSubgroupData P K hKH
  have hfirst := mobiusTriangleGroup_actual_firstKind Q.asFuchsianDisc hTri
  have hFG := mobiusTriangleGroup_finitelyGenerated hTri
  obtain ⟨orders₀, cusps₀, hSig₀, hthree₀⟩ :=
    mobiusTriangleGroup_actual_three_marked_signature Q.asFuchsianDisc hTri
  obtain ⟨orders, cusps, hSig, hthree⟩ :=
    fuchsian_three_marked_subgroup_signature P K hKH hfirst hFG orders₀ cusps₀ hSig₀ hthree₀
  have hfirstH := fuchsian_firstKind_of_subgroup P K hKH hfirst
  have hFGH := (fuchsian_firstKind_finitelyGenerated_subgroup_index P K hKH hfirst hFG).2
  exact firstKind_three_marked_signature_isMobiusTriangleGroup P.asFuchsianDisc hFGH
    hfirstH orders cusps hSig hthree

/-- For an arbitrary original Fuchsian disc and actual whole subgroup inclusion. -/
theorem fuchsian_supergroup_of_triangleGroup_is_triangleGroup
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup Mobius.complexMobiusGroup) (hKH : K ≤ H)
    (hTri : IsMobiusTriangleGroup K) : IsMobiusTriangleGroup H := by
  let q := geometricDiscNormalizer D
  let P := geometricDiscData D
  let K' := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K
  have hK'H : K' ≤ geometricDiscGroup D := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q K f).mp hf
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g, hKH hg, rfl⟩
  have hTri' := hTri.conjugation q
  have hH := unitDisc_triangle_overgroup_isMobiusTriangleGroup P K' hK'H hTri'
  exact isMobiusTriangleGroup_of_conjugate H q hH

/-- The original discrete conformal half-plane assertion. -/
theorem halfPlane_supergroup_of_triangleGroup_is_triangleGroup
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H)
    (K : Subgroup Mobius.complexMobiusGroup)
    (hKH : K ≤ H)
    (hTri : IsMobiusTriangleGroup K) : IsMobiusTriangleGroup H :=
  fuchsian_supergroup_of_triangleGroup_is_triangleGroup P.asFuchsianDisc K hKH hTri

end LowDimensionalTopology.Geometry.Fuchsian
