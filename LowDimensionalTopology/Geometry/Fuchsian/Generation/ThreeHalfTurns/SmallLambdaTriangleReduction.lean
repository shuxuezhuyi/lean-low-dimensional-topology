/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.FuchsianCuspCompletion
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
public import Mathlib.Topology.Connected.Clopen
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnCovering
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleSignatureProfile
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.HalfTurnExceptionalTriples
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnUniversalBound
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspCompletionConjugacy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint
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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuinely compact original quotient has no actual parabolic cusp class:
its open image in the connected Hausdorff cusp completion is also closed. -/
theorem compactCusps_classes_isEmpty_of_compact_quotient
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    [CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain)] :
    IsEmpty (FuchsianCyclicConjugacyClasses D .parabolic) := by
  let : T2Space (FuchsianCuspCompletion D):=fuchsianCuspCompletion_t2Space D
  let : ConnectedSpace (FuchsianCuspCompletion D):=fuchsianCuspCompletion_connectedSpace D
  let i:=fuchsianCuspCompletionOld D
  have hi : Topology.IsOpenEmbedding i:=fuchsianCuspCompletionOld_isOpenEmbedding D
  have hc : IsClosed (range i):=(isCompact_range hi.continuous).isClosed
  have ho : IsOpen (range i):=hi.isOpenMap.isOpen_range
  have hall : range i=univ:=IsClopen.eq_univ ⟨hc,ho⟩ (Set.range_nonempty i)
  refine ⟨fun c=>?_⟩
  exact fuchsianCuspCompletionPoint_not_mem_old D c (by rw [hall];trivial)

/-- The actual compact whole-orbit cover maps onto the unchanged original
half-plane quotient by the literal continuous original orbit projection. -/
theorem compactCusps_original_quotient_compact
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (C : Set ℍ) (hC : IsCompact C) :
    letI:=P.nativeAction
    (∀z : ℍ,∃g : H,g • z∈C) →
      CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain) := by
  let nativeCompactCuspsAction:=P.nativeAction
  intro hcover
  let D:=P.asFuchsianDisc
  let E : ℍ≃ₜD.domain.carrier:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph
  have he (g : H) (z : ℍ) : E (g • z)=g • E z:=by
    apply Subtype.ext
    change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g • z)=g.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)
    exact (P.nativeAction_boundary g z).symm
  have himage : (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain ∘ E) '' C=univ:=by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x,rfl⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_surjective D.domain q
    obtain ⟨g,hg⟩:=hcover (E.symm x)
    refine ⟨g • E.symm x,hg,?_⟩
    change _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain (E (g • E.symm x))=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain x
    rw [he,E.apply_symm_apply,_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_smul]
  have hcomp:=hC.image ((_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection_continuous D.domain).comp E.continuous)
  rw [himage] at hcomp
  exact isCompact_univ_iff.mp hcomp

/-- Actual compact orbit coverage rules out every true cusp class of the
original half-plane Fuchsian group, without a no-parabolic premise. -/
theorem compactCusps_original_classes_isEmpty
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (C : Set ℍ) (hC : IsCompact C) :
    letI:=P.nativeAction
    (∀z : ℍ,∃g : H,g • z∈C) →
      IsEmpty (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) := by
  let nativeCompactCuspsAction:=P.nativeAction
  intro hcover
  let : CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.asFuchsianDisc.domain):=
    compactCusps_original_quotient_compact P C hC hcover
  exact compactCusps_classes_isEmpty_of_compact_quotient P.asFuchsianDisc

/-- The original actual maximal parabolic conjugacy-class count is zero. -/
theorem compactCusps_original_class_count
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (C : Set ℍ) (hC : IsCompact C) :
    letI:=P.nativeAction
    (∀z : ℍ,∃g : H,g • z∈C) →
      Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)=0 := by
  let nativeCompactCuspsAction:=P.nativeAction
  intro hcover
  exact Nat.card_eq_zero.mpr (Or.inl (compactCusps_original_classes_isEmpty P C hC hcover))

/-- The faithful actual boundary image of a discrete native conformal group
inherits the proved absence of genuine cusp classes from its actual compact orbit cover. -/
theorem compactCusps_native_classes_isEmpty (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (C : Set ℍ)
    (hC : IsCompact C)
    (hcover : ∀z : ℍ,∃g : H,g • z∈C) :
    IsEmpty (FuchsianCyclicConjugacyClasses
      (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc .parabolic) := by
  let P:=nativeConformalSubgroup_halfPlaneData H hConf
  let nativeCompactCuspsOriginalAction:=P.nativeAction
  let F:=nativeConformalSubgroupMobiusHom H hConf
  have hJcover (z : ℍ) : ∃g : F.range,g • z∈C:=by
    obtain ⟨g,hg⟩:=hcover z
    refine ⟨F.rangeRestrict g,?_⟩
    have he : (F.rangeRestrict g) • z=g • z:=by
      apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
      rw [←P.nativeAction_boundary]
      exact nativeConformalSubgroupMobiusHom_action H hConf g z
    rwa [he]
  exact compactCusps_original_classes_isEmpty P C hC hJcover

/-- The same genuine cusp count vanishes for the unchanged native action's
faithful original boundary group. -/
theorem compactCusps_native_class_count (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (C : Set ℍ)
    (hC : IsCompact C)
    (hcover : ∀z : ℍ,∃g : H,g • z∈C) :
    Nat.card (FuchsianCyclicConjugacyClasses
      (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc .parabolic)=0 :=
  Nat.card_eq_zero.mpr (Or.inl (compactCusps_native_classes_isEmpty H hConf C hC hcover))

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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open MeasureTheory
open scoped ENNReal

/-- A genuine compact whole-orbit cover supplies the actual original signature
with zero cusps, and its area is precisely the unchanged native covolume. -/
theorem compactSignature_native_compact_cover
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (C : Set ℍ)
    (hC : IsCompact C)
    (hcover : ∀z : ℍ,∃g : H,g • z∈C) :
    ∃g : ℕ,∃orders : List ℕ,
      HasCofiniteFuchsianSignature
        (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc g orders 0 ∧
      (MeasureTheory.covolume H ℍ volume).toReal=2*Real.pi*(2*(g : ℝ)-2+
        (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum) ∧
      0<MeasureTheory.covolume H ℍ volume ∧
      MeasureTheory.covolume H ℍ volume≠⊤ ∧
      0<(MeasureTheory.covolume H ℍ volume).toReal := by
  let P:=nativeConformalSubgroup_halfPlaneData H hConf
  let nativeCompactSignatureOriginalAction:=P.nativeAction
  let e:=nativeCovolume_groupEquiv H hConf
  have hJcover (z : ℍ) : ∃g : (nativeConformalSubgroupMobiusHom H hConf).range,g • z∈C:=by
    obtain ⟨g,hg⟩:=hcover z
    exact ⟨e g,(nativeCovolume_groupEquiv_action H hConf g z).symm ▸ hg⟩
  obtain ⟨F,hF,hpos,_hle,hfin⟩:=compactCover_native_finite_positive_fundamental P C hC hJcover
  have hMFJ:=native_geometric_fundamental_measureDomain P F hF
  have hMF:=nativeCovolume_measureDomain_transport H hConf F hMFJ
  let : Countable H:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeDiscreteIsometrySubgroup_countable H
  let : ContinuousConstSMul H ℍ:=⟨fun g=>g.val.continuous⟩
  have hcov : MeasureTheory.covolume H ℍ volume=volume F:=hMF.covolume_eq_volume volume
  have hgeom:=P.geometric_fundamental hF
  have harea:=compactCover_original_geometric_area P F hF.isOpen.measurableSet
  have hgeomFin : geometricModelArea P.asFuchsianDisc
      (geometricHalfPlaneIdentity P.asFuchsianDisc rfl ⁻¹' F)≠⊤:=by
    rw [harea]
    exact hfin
  obtain ⟨g₀,orders₀,cusps₀,hSig₀⟩:=
    finite_area_actual_cofinite_signature_exists P.asFuchsianDisc _ hgeom hgeomFin
  let _compactSignatureActualEllipticFinite :
      Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_area_elliptic_classes_finite P.asFuchsianDisc _ hgeom hgeomFin
  obtain ⟨g,hgenus,hA⟩:=
    finite_area_original_actual_signature_area P.asFuchsianDisc _ hgeom hgeomFin
  have hcusps : Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)=0:=
    compactCusps_original_class_count P C hC hJcover
  refine ⟨g,fuchsianEllipticOrderList P.asFuchsianDisc,?_,?_,?_,?_,?_⟩
  · exact {
      ellipticClassesFinite:=_compactSignatureActualEllipticFinite
      parabolicClassesFinite:=hSig₀.parabolicClassesFinite
      compact:=hSig₀.compact
      topologicalGenus:=hgenus
      ellipticOrders:=List.Perm.refl _
      cuspCount:=hcusps.symm }
  · rw [harea,hcusps] at hA
    rw [hcov]
    simpa only [Nat.cast_zero,add_zero] using hA
  · rwa [hcov]
  · rwa [hcov]
  · exact ENNReal.toReal_pos (by rw [hcov];exact ne_of_gt hpos) (by rw [hcov];exact hfin)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- One specified actual cone order strengthens the elementary half-counting estimate. -/
theorem halfTurn_marked_cone_sum_lower (orders : List ℕ) (h2 : ∀m∈orders,2≤m)
    (n : ℕ) (hn : n∈orders) :
    (orders.length : ℝ)/2+1/2-1/(n : ℝ)≤
      (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum := by
  induction orders with
  | nil=>simp at hn
  | cons m tail ih=>
    have ht : ∀k∈tail,2≤k:=fun k hk=>h2 k (by simp only [List.mem_cons];exact Or.inr hk)
    have hm:=signature_elliptic_weight_bounds m (h2 m (by simp))
    simp only [List.mem_cons] at hn
    rcases hn with rfl|hn
    · have hh:=signature_elliptic_sum_lower tail ht
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
      linarith only [hh]
    · have hh:=ih ht hn
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
      linarith only [hm.1,hh]

/-- The exact covering equation and the true product-order entry rule out
positive genus and every cone count other than three in the nonprimitive branch. -/
theorem halfTurn_cover_small_signature_structure (g : ℕ) (orders : List ℕ)
    (h2 : ∀m∈orders,2≤m) (p q N n : ℕ) (hp : 2≤p) (hpq : 2*p<q) (hN : p≤N)
    (hn : n∈orders) (hqn : q≤n)
    (hpos : 0<2*(g : ℝ)-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum)
    (hArea : 2*(N : ℝ)*(2*(g : ℝ)-2+
      (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum)=1-2*(p : ℝ)/q) :
    g=0 ∧ orders.length=3 := by
  let δ:=2*(g : ℝ)-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum
  have hδ : 0<δ:=hpos
  have hp0 : 0<(p : ℝ):=by exact_mod_cast (show 0<p by omega)
  have hq0 : 0<(q : ℝ):=by exact_mod_cast (show 0<q by omega)
  have hN2 : (2 : ℝ)≤N:=by exact_mod_cast (show 2≤N by omega)
  have hbound : δ<1/4:=by
    have hnon : 0≤((N : ℝ)-2)*δ:=mul_nonneg (sub_nonneg.mpr hN2) hδ.le
    have hratio : 0<2*(p : ℝ)/q:=by positivity
    change 2*(N : ℝ)*δ=1-2*(p : ℝ)/q at hArea
    nlinarith only [hnon,hArea,hratio]
  have hlo:=signature_elliptic_sum_lower orders h2
  have hlne : orders≠[]:=by intro he;simp only [he,List.not_mem_nil] at hn
  have hlen1 : (1 : ℝ)≤orders.length:=by
    exact_mod_cast (List.length_pos_iff.mpr hlne)
  have hg : g=0:=by
    by_contra hg
    have hg1 : (1 : ℝ)≤g:=by exact_mod_cast (show 1≤g by omega)
    dsimp only [δ] at hbound
    linarith only [hbound,hlo,hlen1,hg1]
  have hsumUpper:=signature_elliptic_sum_lt_length orders h2 hlne
  have hl3 : 3≤orders.length:=by
    have hh : (2 : ℝ)<orders.length:=by
      dsimp only [δ] at hδ
      rw [hg] at hδ
      norm_num only [Nat.cast_zero,mul_zero,zero_sub] at hδ
      linarith only [hδ,hsumUpper]
    exact_mod_cast (show (3 : ℕ)≤orders.length by exact Nat.succ_le_of_lt (by exact_mod_cast hh))
  have hn0 : 0<(n : ℝ):=lt_of_lt_of_le hq0 (by exact_mod_cast hqn)
  have hrecip : 1/(n : ℝ)≤1/(q : ℝ):=
    one_div_le_one_div_of_le hq0 (by exact_mod_cast hqn)
  have hm:=halfTurn_marked_cone_sum_lower orders h2 n hn
  have hlen4 : ¬4≤orders.length:=by
    intro hlen4
    have hl4 : (4 : ℝ)≤orders.length:=by exact_mod_cast hlen4
    have hδlow : 1/2-1/(n : ℝ)≤δ:=by
      dsimp only [δ]
      rw [hg]
      norm_num only [Nat.cast_zero,mul_zero,zero_sub]
      linarith only [hm,hl4]
    have hNp : (p : ℝ)≤N:=by exact_mod_cast hN
    have hprod : 0≤((N : ℝ)-(p : ℝ))*δ:=mul_nonneg (sub_nonneg.mpr hNp) hδ.le
    have hmul:=mul_le_mul_of_nonneg_left hδlow (by positivity : 0≤2*(p : ℝ))
    have hrecipmul:=mul_le_mul_of_nonneg_left hrecip (by positivity : 0≤2*(p : ℝ))
    change 2*(N : ℝ)*δ=1-2*(p : ℝ)/q at hArea
    have hp2 : (2 : ℝ)≤p:=by exact_mod_cast hp
    have hratio : 2*(p : ℝ)/q=2*(p : ℝ)*(1/(q : ℝ)):=by ring
    rw [hratio] at hArea
    nlinarith only [hArea,hprod,hmul,hrecipmul,hp2]
  exact ⟨hg,by omega⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
open MeasureTheory
open scoped ENNReal

/-- The actual nonprimitive reduced numerator forces genus zero and exactly
three genuine cone classes in the unchanged faithful boundary group. -/
theorem halfTurnCanonical_nonprimitive_signature
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
        2*(N : ℝ)*(-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum)=1-2*(p : ℝ)/q := by
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
  refine ⟨orders,hSig,hlen,N,n,hN,hDegree,hnmem,hdiv,?_⟩
  simpa only [δ,Nat.cast_zero,mul_zero,zero_sub] using hAreaScalar

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- A specified entry of a genuine three-cone list can be placed last while
ordering only the other two actual cone entries. -/
theorem halfTurn_three_orders_marked_last (orders : List ℕ)
    (hlen : orders.length=3) (n : ℕ) (hn : n∈orders) :
    ∃l m : ℕ,l≤m ∧ [l,m,n].Perm orders := by
  obtain ⟨a,b,c,rfl⟩:=List.length_eq_three.mp hlen
  have h (a b : ℕ) (hp : [a,b,n].Perm [a,b,c]) :
      ∃l m : ℕ,l≤m ∧ [l,m,n].Perm [a,b,c] := by
    rcases le_total a b with hab|hba
    · exact ⟨a,b,hab,hp⟩
    · exact ⟨b,a,hba,(List.Perm.swap a b [n]).trans hp⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl
  · rcases le_total b c with hbc|hcb
    · exact ⟨b,c,hbc,by simpa using (List.perm_append_comm (l₁:=[b,c]) (l₂:=[n]))⟩
    · refine ⟨c,b,hcb,?_⟩
      exact (List.Perm.swap b c [n]).trans (by
        simpa using (List.perm_append_comm (l₁:=[b,c]) (l₂:=[n])))
  · rcases le_total a c with hac|hca
    · exact ⟨a,c,hac,(List.Perm.swap n c []).cons a⟩
    · exact ⟨c,a,hca,(List.Perm.swap a c [n]).trans ((List.Perm.swap n c []).cons a)⟩
  · exact h a b (List.Perm.refl _)

/-- The actual covering equation forces the complete exceptional three-cone
order lists and reduced numerator possibilities. -/
theorem halfTurn_nonprimitive_order_list_classification (orders : List ℕ)
    (h2 : ∀m∈orders,2≤m) (hlen : orders.length=3)
    (p q N n : ℕ) (hp : 2≤p) (hpq : 2*p<q) (hN : p≤N)
    (hn : n∈orders) (hqn : q≤n)
    (hArea : 2*(N : ℝ)*(-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum)=
      1-2*(p : ℝ)/q) :
    (p=2 ∧ orders.Perm [2,3,n] ∧ 7≤n) ∨
    (p=3 ∧ orders.Perm [2,3,n] ∧ 7≤n) ∨
    (p=2 ∧ orders.Perm [2,4,n] ∧ 5≤n) := by
  obtain ⟨l,m,hlm,hperm⟩:=halfTurn_three_orders_marked_last orders hlen n hn
  have hl : 2≤l:=h2 l (hperm.mem_iff.mp (by simp))
  have hm : 2≤m:=h2 m (hperm.mem_iff.mp (by simp))
  have hn2 : 2≤n:=h2 n hn
  have hsum: (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum=
      3-(1/(l : ℝ)+1/(m : ℝ)+1/(n : ℝ)):=by
    rw [←(hperm.map (fun m : ℕ=>1-1/(m : ℝ))).sum_eq]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring
  rw [hsum] at hArea
  let δ:ℝ:=1-(1/(l : ℝ)+1/(m : ℝ)+1/(n : ℝ))
  have hpR : 0<(p : ℝ):=by exact_mod_cast (show 0<p by omega)
  have hqR : 0<(q : ℝ):=by exact_mod_cast (show 0<q by omega)
  have hNR : 0<(N : ℝ):=by exact_mod_cast (show 0<N by omega)
  have hnr : 0<(n : ℝ):=by exact_mod_cast (show 0<n by omega)
  have hpqR : 2*(p : ℝ)<q:=by exact_mod_cast hpq
  have hArea' : 2*(N : ℝ)*δ=1-2*(p : ℝ)/q:=by dsimp only [δ];linarith only [hArea]
  have hrat : 0<1-2*(p : ℝ)/q:=by
    have hh:2*(p : ℝ)/q<1:=(div_lt_one hqR).mpr hpqR
    linarith only [hh]
  have hδ : 0<δ:=by nlinarith only [hArea',hrat,hNR]
  have hproper : 1/(l : ℝ)+1/(m : ℝ)+1/(n : ℝ)<1:=by
    dsimp only [δ] at hδ
    linarith only [hδ]
  have hdiff : 0≤((N : ℝ)-(p : ℝ))*δ:=
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hN)) hδ.le
  have hrecip : 1/(n : ℝ)≤1/(q : ℝ):=
    one_div_le_one_div_of_le hqR (by exact_mod_cast hqn)
  have hmul:=mul_le_mul_of_nonneg_left hrecip (show 0≤2*(p : ℝ) by positivity)
  have hbudget : 2*(p : ℝ)*(1-(1/(l : ℝ)+1/(m : ℝ)+1/(n : ℝ)))≤
      1-2*(p : ℝ)/n:=by
    have hq:2*(p : ℝ)/q=2*(p : ℝ)*(1/(q : ℝ)):=by ring
    have hn:2*(p : ℝ)/n=2*(p : ℝ)*(1/(n : ℝ)):=by ring
    rw [hq] at hArea'
    rw [hn]
    change 2*(p : ℝ)*δ≤_
    nlinarith only [hArea',hdiff,hmul]
  have hex:=halfTurn_first_last_area_exceptional_triples l m n p hl hlm hn2 hp hproper hbudget
  have hn23 (hl:l=2) (hm:m=3) : 7≤n:=by
    by_contra hh
    have hn6:n≤6:=by omega
    interval_cases n <;> norm_num [hl,hm] at hproper
  have hn24 (hl:l=2) (hm:m=4) : 5≤n:=by
    by_contra hh
    have hn4:n≤4:=by omega
    interval_cases n <;> norm_num [hl,hm] at hproper
  rcases hex with he|he|he <;> simp only [Prod.mk.injEq] at he
  · rcases he with ⟨hl,hm,hp⟩
    exact Or.inl ⟨hp,by simpa only [hl,hm] using hperm.symm,hn23 hl hm⟩
  · rcases he with ⟨hl,hm,hp⟩
    exact Or.inr (Or.inl ⟨hp,by simpa only [hl,hm] using hperm.symm,hn23 hl hm⟩)
  · rcases he with ⟨hl,hm,hp⟩
    exact Or.inr (Or.inr ⟨hp,by simpa only [hl,hm] using hperm.symm,hn24 hl hm⟩)


theorem halfTurnCanonical_nonprimitive_order_classification
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
    (p=2 ∨ p=3) ∧
      ((∃n : ℕ,7≤n ∧ HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,3,n] 0) ∨
       (∃n : ℕ,5≤n ∧ HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,4,n] 0)) := by
  obtain ⟨orders,hSig,hlen,N,n,_hN,hDegree,hnmem,hdiv,hArea⟩:=
    halfTurnCanonical_nonprimitive_signature u t hu hut w hw hn hc hd p q hp hpq hq hθ
  have hn2:=hSig.orders_two_le hnmem
  have hqn : q≤n:=Nat.le_of_dvd (by omega) hdiv
  have hC:=halfTurn_nonprimitive_order_list_classification orders
    (fun _ hm=>hSig.orders_two_le hm) hlen p q N n hp hpq hDegree hnmem hqn hArea
  rcases hC with ⟨hp2,hperm,hn7⟩|⟨hp3,hperm,hn7⟩|⟨hp2,hperm,hn5⟩
  · exact ⟨Or.inl hp2,Or.inl ⟨n,hn7,hSig.perm_orders hperm.symm⟩⟩
  · exact ⟨Or.inr hp3,Or.inl ⟨n,hn7,hSig.perm_orders hperm.symm⟩⟩
  · exact ⟨Or.inl hp2,Or.inr ⟨n,hn5,hSig.perm_orders hperm.symm⟩⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane OnePoint MatrixGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Equality of genuine real absolute traces preserves the exact order of
nonidentity transformations, through the proved actual conjugacy theorem. -/
theorem halfTurn_real_abs_trace_order_eq
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (ht : |Matrix.trace A.val|=|Matrix.trace B.val|) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
  have hs:(Matrix.trace A.val)^2=(Matrix.trace B.val)^2:=by
    have he:=congrArg (fun r:ℝ=>r^2) ht
    rw [sq_abs,sq_abs] at he
    exact he
  have hc:IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_isConj_iff_squaredTrace_eq _ _ hA hB).mpr (by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace]
      exact congrArg (fun r:ℝ=>(r:ℂ)) hs)
  obtain ⟨q,hq⟩:=isConj_iff.mp hc
  have he:orderOf (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*q⁻¹)=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=
    (MulAut.conj q).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  rw [hq] at he
  exact he.symm

/-- The actual radial and integer half-period reductions preserve the
entire original generated group and the exact order of its product.
No normalization or product-order premise is supplied. -/
theorem halfTurn_actual_halfperiod_group_model (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A T.a)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B T.b)
    (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup))) :
    ∃(r:Matrix.SpecialLinearGroup (Fin 2) ℝ)(u t:ℝ)(hu:0<u)(ht:1<t)(w:ℍ),
      1≤u ∧ u<t ∧ 0<w.re ∧ w.re^2+w.im^2=t^2 ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r)
        (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)}:Set Mobius.complexMobiusGroup)) ∧
      |Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|=
        |Matrix.trace (A*B*C).val| ∧
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=
        orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C)) := by
  obtain ⟨r,u,v,hu,hv,w,huv,hw,hn,hG,htr⟩:=
    three_halfturn_actual_radial_axis_normalization T A B C hA hB hC
  have ht:1<v/u:=(one_lt_div hu).mpr huv
  let : DiscreteTopology (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup)):=hd
  have hdc:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r)
    (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup))
  change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r)
    (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup))) at hdc
  rw [hG] at hdc
  obtain ⟨k,a,b,ha,hb,_hae,hbe,ha1,hat,_hab,hGrp,hTrace,_hFm,_hGm⟩:=
    three_halfturn_axis_halfperiod_reduction u v hu huv w
  subst b
  have hnewTrace:|Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL a ha*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (a*(v/u)) hb*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|=|Matrix.trace (A*B*C).val|:=by
    calc
      _=|Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|:=
        congrArg abs hTrace
      _=2*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T:=htr
      _=|Matrix.trace (A*B*C).val|:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T A B C hA hB hC).symm
  refine ⟨r,a,v/u,ha,ht,w,ha1,hat,hw,hn,?_,?_,hnewTrace,?_⟩
  · rw [hGrp]
    exact hG
  · rw [hGrp]
    exact hdc
  · apply halfTurn_real_abs_trace_order_eq _ _ _
      (halfTurn_triple_ne_one A B C T.a T.b T.c hA hB hC) hnewTrace
    exact halfTurn_triple_ne_one _ _ _ _ _ w
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at a ha) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at (a*(v/u)) hb) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w)

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

/-- The genuine signature of the native group of three actual matrix actions
pulls back to the unchanged original group and its whole original disc. -/
theorem threeHalfTurn_original_signature_of_native
    {H:Subgroup Mobius.complexMobiusGroup} (D:FuchsianDisc H)
    (A B C:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup)))
    (r:Mobius.complexMobiusGroup)
    (hG:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate r H=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup))
    (hD:r.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (genus cusps:ℕ) (orders:List ℕ)
    (hSig:
      letI:=threeHalfTurn_native_group_discrete_of_original A B C hd
      HasCofiniteFuchsianSignature
        (nativeConformalSubgroup_halfPlaneData
          (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C}:Set (ℍ≃ᵢℍ)))
          (threeHalfTurn_native_group_conformal A B C)).asFuchsianDisc genus orders cusps) :
    HasCofiniteFuchsianSignature D genus orders cusps := by
  let : DiscreteTopology
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C}:Set (ℍ≃ᵢℍ))):=
    threeHalfTurn_native_group_discrete_of_original A B C hd
  let N:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C}:Set (ℍ≃ᵢℍ))
  let hConf:=threeHalfTurn_native_group_conformal A B C
  let P:=nativeConformalSubgroup_halfPlaneData N hConf
  have hRange:=threeHalfTurn_native_group_mobius_image A B C
  have hGroup:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate r H=
      (nativeConformalSubgroupMobiusHom N hConf).range:=hG.trans hRange.symm
  apply cofinite_signature_of_conjugate_group P.asFuchsianDisc D r⁻¹ ?_ ?_
    genus cusps orders hSig
  · rw [←hGroup,_root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel]
  · change r.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier
    rw [←hD]
    exact r.val.symm_image_image D.carrier

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane OnePoint MatrixGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- For the unchanged original disc, a small actual product trace and a
nonprimitive acute product rotation force a genuine triangular signature.
The rotation condition uses the exact order of the original product; no
normalization, numerator, signature or covering data are supplied. -/
theorem threeHalfTurn_original_nonprimitive_triangle_signature
    (f g h : Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)))
    (hf : orderOf f=2) (hg : orderOf g=2) (hh : orderOf h=2)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h} : Set Mobius.complexMobiusGroup)))
    (hsmall : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)<2)
    (hnonprim : Real.pi/(orderOf (f*g*h):ℝ)<
      Real.arccos (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2)) :
    (∃n : ℕ,7≤n ∧ HasCofiniteFuchsianSignature D 0 [2,3,n] 0) ∨
    (∃n : ℕ,5≤n ∧ HasCofiniteFuchsianSignature D 0 [2,4,n] 0) := by
  let F : Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup):=
    ⟨f,Subgroup.subset_closure (by simp)⟩
  let G : Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup):=
    ⟨g,Subgroup.subset_closure (by simp)⟩
  let K : Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup):=
    ⟨h,Subgroup.subset_closure (by simp)⟩
  let A:=D.normalizedLift F
  let B:=D.normalizedLift G
  let C:=D.normalizedLift K
  let q₀:=D.halfPlaneNormalizer
  have hA : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q₀).orderOf_eq f).trans hf
  have hB : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q₀).orderOf_eq g).trans hg
  have hC : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q₀).orderOf_eq h).trans hh
  have hgroup : D.normalizedGroup=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup):=by
    change (Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup)).map
      (MulAut.conj q₀).toMonoidHom=_
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_insert_eq,Set.image_singleton]
    change Subgroup.closure {q₀*f*q₀⁻¹,q₀*g*q₀⁻¹,q₀*h*q₀⁻¹}=_
    rw [←D.normalizedLift_spec F,←D.normalizedLift_spec G,←D.normalizedLift_spec K]
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact D.normalizedGroup_discrete
  have hNE' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact hNE.conjugation q₀
  have hprod : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C)=q₀*(f*g*h)*q₀⁻¹:=by
    dsimp only [A,B,C]
    rw [map_mul,map_mul,D.normalizedLift_spec,D.normalizedLift_spec,D.normalizedLift_spec]
    change (q₀*f*q₀⁻¹)*(q₀*g*q₀⁻¹)*(q₀*h*q₀⁻¹)=q₀*(f*g*h)*q₀⁻¹
    group
  have habs : |Matrix.trace (A*B*C).val|=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs, hprod,
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs,
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation]
    rfl
  have horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C))=orderOf (f*g*h):=by
    rw [hprod]
    exact (MulAut.conj q₀).orderOf_eq (f*g*h)
  obtain ⟨T,hAt,hBt,hCt⟩:=threeHalfTurn_original_centers_triangle A B C hA hB hC hNE'
  obtain ⟨r,u,t,hu,ht,w,hu1,hut,hw,hn,hG,hdisc,htrace,hord⟩:=
    halfTurn_actual_halfperiod_group_model T A B C hAt hBt hCt hd
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu
  let V:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  have htrace' : |Matrix.trace (U*V*W).val|=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h):=htrace.trans habs
  have hord' : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (U*V*W))=orderOf (f*g*h):=hord.trans horder
  have hsmall' : |Matrix.trace (U*V*W).val|<2:=by rwa [htrace']
  change |Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|<2 at hsmall'
  rw [axisHalfTurns_point_triple_trace] at hsmall'
  have hratio : (u*t)/u-u/(u*t)=t-1/t:=by field_simp
  rw [hratio] at hsmall'
  have hscalar:=halfTurn_small_trace_compact_scalar t w.re w.im ht hw w.im_pos hn
    ((le_abs_self _).trans_lt hsmall')
  have hc : t^2+1<2*(t^2/w.re):=by
    have hh' : t^2+1<(2*t^2)/w.re:=(lt_div_iff₀ hw).mpr hscalar
    simpa only [mul_div_assoc] using hh'
  let lam:=halfTurnQuadKleinB (t^2) (t^2/w.re)/
    Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
      (halfTurnQuadKleinA (t^2) (t^2/w.re))^2)
  have hb:=halfTurnQuadCanonical_angles (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2:ℕ)≠0)) hc
  have htr : |Matrix.trace (U*V*W).val|=2*lam:=by
    rw [halfTurnCanonical_trace u t hu ht w hw hn,
      abs_of_pos (mul_pos (by norm_num) hb.1)]
  have hlam : lam=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2:=by linarith only [htr,htrace']
  obtain ⟨p,q,hq,hp,hpq,_hcop,hθ⟩:=
    halfTurnCanonical_reduced u t hu ht w hw hn hc hdisc
  have hq' : q=orderOf (f*g*h):=hq.trans hord'
  have hp2 : 2≤p:=by
    by_contra he
    have hp1 : p=1:=by omega
    have heq : Real.arccos (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2)=
        Real.pi/(orderOf (f*g*h):ℝ):=by
      rw [←hlam]
      rw [hθ,hp1,hq']
      norm_num
    exact (ne_of_lt hnonprim) heq.symm
  have hclass:=halfTurnCanonical_nonprimitive_order_classification
    u t hu1 hut w hw hn hc hdisc p q hp2 hpq hq hθ
  let s:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀
  have hGs : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate s (Subgroup.closure ({f,g,h}:Set Mobius.complexMobiusGroup))=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius U,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius V,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W}:Set Mobius.complexMobiusGroup):=by
    rw [show s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀ by rfl,
      ←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose]
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r) D.normalizedGroup=_
    rw [hgroup]
    exact hG
  have hDs : s.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀).val) '' D.carrier=_
    rw [show (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀).val=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r).val*q₀.val by rfl,
      Equiv.Perm.coe_mul,Function.comp_def,←Set.image_image,D.halfPlaneNormalizer_image,
      realSLMobius_image_openHalfPlane]
  rcases hclass.2 with ⟨n,hn7,hSig⟩|⟨n,hn5,hSig⟩
  · exact Or.inl ⟨n,hn7,threeHalfTurn_original_signature_of_native D U V W
      hdisc s hGs hDs 0 0 [2,3,n] hSig⟩
  · exact Or.inr ⟨n,hn5,threeHalfTurn_original_signature_of_native D U V W
      hdisc s hGs hDs 0 0 [2,4,n] hSig⟩

end LowDimensionalTopology.Geometry.Fuchsian
