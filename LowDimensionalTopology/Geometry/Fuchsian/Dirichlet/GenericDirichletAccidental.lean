/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.CyclicDiscCircles
public import LowDimensionalTopology.Geometry.Mobius.Algebraic.OrbitCrossRatioPolynomials
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAccidentalCycles
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.EllipticPencils
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
/-- An original generated pair sharing an actual fixed point is a subgroup of the actual cyclic point stabilizer. -/
theorem unitDisc_common_fixed_pair_isCyclic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H) (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hf : f.val.val ξ=ξ) (hg : g.val.val ξ=ξ) :
    IsCyclic (Subgroup.closure ({f.val,g.val} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
  let : IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
    ξ):=P.asFuchsianDisc.stabilizer_isCyclic ξ
  apply Subgroup.isCyclic_of_le (H':=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ξ)
  apply (Subgroup.closure_le _).mpr
  intro k hk
  rcases hk with rfl|rfl
  · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ξ
    f.val).mpr ⟨f.property,hf⟩
  · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ξ
    g.val).mpr ⟨g.property,hg⟩

/-- A genuine free center identifies distinct original group elements with distinct actual orbit points. -/
theorem dirichletCenter_orbit_injective {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w) :
    Function.Injective (fun g : H=>g • w):=by
  intro f g hfg
  change f • w=g • w at hfg
  have hfix : (g⁻¹*f) • w=w:=by rw [mul_smul,hfg,inv_smul_smul]
  have h1:=hw (g⁻¹*f) hfix
  exact (eq_of_inv_mul_eq_one h1).symm

/-- Four distinct actual orbit points on an accidental-centered true circle force the original rational ratio to be nonconstant. -/
theorem dirichlet_circle_orbitRatio_nonconstant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (u : P.domain.carrier) (hu : IsAccidentalFuchsianPoint P u) (f g h : H)
    (hf : f≠1) (hg : g≠1) (hh : h≠1) (hfg : f≠g) (hfh : f≠h) (hgh : g≠h)
    (A B C : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hA :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A=f.val)
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B=g.val) (hC :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection C=h.val)
    (r : ℝ) (h0 : P.hyperbolicDist u w=r)
    (hfd : P.hyperbolicDist u (f • w)=r) (hgd : P.hyperbolicDist u (g • w)=r)
    (hhd : P.hyperbolicDist u (h • w)=r) :
    ¬∃c : ℂ,_root_.LowDimensionalTopology.Geometry.Mobius.orbitRatioNumerator 1 A B C=Polynomial.C c*_root_.LowDimensionalTopology.Geometry.Mobius.orbitRatioDenominator 1 A B C:=by
  intro hc
  obtain ⟨z,hgz,hother⟩:=_root_.LowDimensionalTopology.Geometry.Mobius.unitDisc_constantOrbitRatio_common_fixed P f g h A B C hA hB hC hg hfh hc
  have huFree : IsDirichletCenter P u:=(isAccidentalFuchsianPoint_iff_no_stabilizer P u).mp hu
  have hn (k : H) (hk : k≠1) : w≠k • w:=by intro he;exact hk (hw k he.symm)
  have hinj:=dirichletCenter_orbit_injective P w hw
  rcases hother with hfz|hhz
  · have hcyc:=unitDisc_common_fixed_pair_isCyclic P g f (z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hgz hfz
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cyclicDisc_pair_not_cyclic P u huFree w g f r h0 hgd hfd (hn
      g hg) (hn f hf)
      (fun he=>hfg (hinj he).symm) hcyc
  · have hcyc:=unitDisc_common_fixed_pair_isCyclic P g h (z :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hgz hhz
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cyclicDisc_pair_not_cyclic P u huFree w g h r h0 hgd hhd (hn
      g hg) (hn h hh)
      (fun he=>hgh (hinj he)) hcyc

/-- Four actual original points at the same positive genuine metric radius have real ordered cross-ratio. -/
theorem unitDisc_metric_circle_crossRatio_real {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (u a b c d : P.domain.carrier) (r : ℝ) (hr : 0<r)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.QuadrupleDistinct a.val b.val c.val d.val)
    (ha : P.hyperbolicDist u a=r) (hb : P.hyperbolicDist u b=r)
    (hc : P.hyperbolicDist u c=r) (hdd : P.hyperbolicDist u d=r) :
    (_root_.LowDimensionalTopology.Geometry.Mobius.extendedCrossRatio a.val b.val c.val d.val).im=0:=by
  let p:=P.halfPlaneCoordinate u
  obtain ⟨C,hC,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hMetricCircle_orthogonal p r hr (.vertical
    p.re) rfl
  have hm (x : P.domain.carrier) (hx : P.hyperbolicDist u x=r) :
      (((P.halfPlaneCoordinate x : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈C.val:=by
    have hmetric : P.halfPlaneCoordinate x∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.hMetricCircle p r:=by
      change dist (P.halfPlaneCoordinate x) p=r
      exact (dist_comm _ _).trans hx
    rw [hC] at hmetric
    exact hmetric
  have hn (x y : P.domain.carrier) (hxy : x.val≠y.val) :
      (((P.halfPlaneCoordinate x : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)≠
        (((P.halfPlaneCoordinate y : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [P.halfPlaneCoordinate_extended,P.halfPlaneCoordinate_extended]
    exact fun he=>hxy (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val.injective he)
  have hd' : _root_.LowDimensionalTopology.Geometry.Mobius.QuadrupleDistinct
      (((P.halfPlaneCoordinate a : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (((P.halfPlaneCoordinate b : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (((P.halfPlaneCoordinate c : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      (((P.halfPlaneCoordinate d : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=
    ⟨hn a b hd.1,hn a c hd.2.1,hn a d hd.2.2.1,
      hn b c hd.2.2.2.1,hn b d hd.2.2.2.2.1,hn c d hd.2.2.2.2.2⟩
  have he:=(_root_.LowDimensionalTopology.Geometry.Mobius.complexConcyclic_iff_crossRatio_real _ _ _ _ hd').mp
    ⟨hd',C.val,C.property,hm a ha,hm b hb,hm c hc,hm d hdd⟩
  have hratio:=_root_.LowDimensionalTopology.Geometry.Mobius.extendedCrossRatio_mobius _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ a.val b.val c.val d.val
  rw [←P.halfPlaneCoordinate_extended,←P.halfPlaneCoordinate_extended,
    ←P.halfPlaneCoordinate_extended,←P.halfPlaneCoordinate_extended] at hratio
  rwa [hratio] at he

/-- A representative is chosen only for constructing countably many actual polynomial exceptions. -/
def orbitMatrixRepresentative (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2:=
  Classical.choose (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection_surjective f)

theorem orbitMatrixRepresentative_spec (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (orbitMatrixRepresentative f)=f:=
  Classical.choose_spec (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection_surjective f)

def orbitTripleNumerator (f g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Polynomial ℂ:=
  _root_.LowDimensionalTopology.Geometry.Mobius.orbitRatioNumerator 1 (orbitMatrixRepresentative
    f) (orbitMatrixRepresentative g) (orbitMatrixRepresentative h)

def orbitTripleDenominator (f g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Polynomial ℂ:=
  _root_.LowDimensionalTopology.Geometry.Mobius.orbitRatioDenominator 1 (orbitMatrixRepresentative
    f) (orbitMatrixRepresentative g) (orbitMatrixRepresentative h)

theorem orbitTripleRatio_eval (f g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (z : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.extendedCrossRatio (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (f.val (z :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
      (g.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (h.val (z :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))=
        (orbitTripleNumerator f g h).eval z/(orbitTripleDenominator f g h).eval z:=by
  have he:=_root_.LowDimensionalTopology.Geometry.Mobius.orbitCrossRatio_polynomial 1 (orbitMatrixRepresentative f)
    (orbitMatrixRepresentative g) (orbitMatrixRepresentative h) z
  simpa only [map_one,Subgroup.coe_one,Equiv.Perm.one_apply,orbitMatrixRepresentative_spec,
    orbitTripleNumerator,orbitTripleDenominator] using he

theorem orbitTripleDenominator_ne_zero (f g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
  f≠1) (hgh : g≠h) :
    orbitTripleDenominator f g h≠0:=by
  apply _root_.LowDimensionalTopology.Geometry.Mobius.orbitRatioDenominator_ne_zero
  · rw [map_one,orbitMatrixRepresentative_spec]
    exact hf.symm
  · rwa [orbitMatrixRepresentative_spec,orbitMatrixRepresentative_spec]

def IsNonconstantOrbitTriple {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (t :
  H×H×H) : Prop:=
  t.1≠1 ∧ t.2.1≠t.2.2 ∧
    ¬∃c : ℂ,orbitTripleNumerator t.1.val t.2.1.val t.2.2.val=
      Polynomial.C c*orbitTripleDenominator t.1.val t.2.1.val t.2.2.val

/-- The actual countable polynomial exceptions; no cycle conclusion enters their definition. -/
def dirichletAccidentalBadCenters {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H) : Set P.domain.carrier:=
  ⋃t : {t : H×H×H // IsNonconstantOrbitTriple t},
    {w | ((orbitTripleNumerator t.val.1.val t.val.2.1.val t.val.2.2.val).eval (P.finiteCoordinate w : ℂ)/
      (orbitTripleDenominator t.val.1.val t.val.2.1.val t.val.2.2.val).eval (P.finiteCoordinate w : ℂ)).im=0}

/-- The actual entire exceptional set has zero genuine hyperbolic area. -/
theorem dirichletAccidentalBadCenters_area_zero {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    P.area (dirichletAccidentalBadCenters P)=0:=by
  let : Countable H:=P.countable
  apply measure_iUnion_null
  intro t
  apply P.rational_real_locus_area_zero
  · apply orbitTripleDenominator_ne_zero
    · exact fun he=>t.property.1 (Subtype.val_injective he)
    · exact fun he=>t.property.2.1 (Subtype.val_injective he)
  · exact t.property.2.2

/-- Every actual four-point accidental-centered orbit circle puts the genuine free center in the proved null exceptional set. -/
theorem mem_dirichletAccidentalBadCenters_of_four_circle {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (u : P.domain.carrier) (hu : IsAccidentalFuchsianPoint P u) (f g h : H)
    (hf : f≠1) (hg : g≠1) (hh : h≠1) (hfg : f≠g) (hfh : f≠h) (hgh : g≠h)
    (r : ℝ) (h0 : P.hyperbolicDist u w=r) (hfd : P.hyperbolicDist u (f • w)=r)
    (hgd : P.hyperbolicDist u (g • w)=r) (hhd : P.hyperbolicDist u (h • w)=r) :
    w∈dirichletAccidentalBadCenters P:=by
  have hnc:=dirichlet_circle_orbitRatio_nonconstant P w hw u hu f g h hf hg hh hfg hfh hgh
    (orbitMatrixRepresentative f.val) (orbitMatrixRepresentative g.val) (orbitMatrixRepresentative h.val)
    (orbitMatrixRepresentative_spec _) (orbitMatrixRepresentative_spec _) (orbitMatrixRepresentative_spec _)
    r h0 hfd hgd hhd
  have hn (k : H) (hk : k≠1) : w.val≠(k • w).val:=by
    intro he
    exact hk (hw k (Subtype.ext he.symm))
  have hinj:=dirichletCenter_orbit_injective P w hw
  have hnf (k l : H) (hkl : k≠l) : (k • w).val≠(l • w).val:=by
    intro he
    exact hkl (hinj (Subtype.ext he))
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.QuadrupleDistinct w.val (f • w).val (g • w).val (h • w).val:=
    ⟨hn f hf,hn g hg,hn h hh,hnf f g hfg,hnf f h hfh,hnf g h hgh⟩
  have hr0 : 0≤r:=by
    change dist (P.halfPlaneCoordinate u) (P.halfPlaneCoordinate w)=r at h0
    rw [←h0]
    exact dist_nonneg
  have hrN : r≠0:=by
    intro he
    have hU : P.halfPlaneCoordinate u=P.halfPlaneCoordinate w:=dist_eq_zero.mp (h0.trans he)
    have hF : P.halfPlaneCoordinate u=P.halfPlaneCoordinate (f • w):=dist_eq_zero.mp (hfd.trans he)
    exact hf (hw f (P.halfPlaneCoordinate.injective (hF.symm.trans hU)))
  have hreal:=unitDisc_metric_circle_crossRatio_real P u w (f • w) (g • w) (h • w) r
    (lt_of_le_of_ne hr0 hrN.symm) hd h0 hfd hgd hhd
  refine mem_iUnion.mpr ⟨⟨(f,g,h),hf,hgh,hnc⟩,?_⟩
  have he:=orbitTripleRatio_eval f.val g.val h.val (P.finiteCoordinate w : ℂ)
  rw [P.finiteCoordinate_extended] at he
  change ((orbitTripleNumerator f.val g.val h.val).eval (P.finiteCoordinate w : ℂ)/
    (orbitTripleDenominator f.val g.val h.val).eval (P.finiteCoordinate w : ℂ)).im=0
  rw [←he]
  exact hreal

/-- Away from the actual null set, every original accidental cycle has at most three points. -/
theorem dirichlet_accidental_cycle_length_le_three {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hwB : w∉dirichletAccidentalBadCenters P) (u : P.domain.carrier)
    (hu : IsAccidentalFuchsianPoint P u) :
    fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) u)≤3:=by
  classical
  by_contra hn
  have h4 : 4≤(fuchsianPolygonCycle P (dirichletDomain P w) u).ncard:=by
    change ¬(fuchsianPolygonCycle P (dirichletDomain P w) u).ncard≤3 at hn
    omega
  let C:=fuchsianPolygonCycle P (dirichletDomain P w) u
  have hC : C.Finite:=(dirichletDomain_isConvexFuchsianPolygon P w hw).locallyFinite.cycle_finite u
  have hc : C.encard=(C.ncard : ℕ∞):=by rw [hC.encard_eq_coe_toFinset_card,Set.ncard_eq_toFinset_card C hC]
  have h4e : (4 : ℕ∞)≤C.encard:=by rw [hc];exact_mod_cast h4
  obtain ⟨v,hv,hvi⟩:=(Set.le_encard_iff_exists_fin_injective C 4).mp h4e
  have horbit (i : Fin 4) : v i∈MulAction.orbit H (v 0):=
    MulAction.mem_orbit_trans (hv i).2 (MulAction.mem_orbit_symm.mp (hv 0).2)
  choose k hk using horbit
  change ∀i,k i • v 0=v i at hk
  have hki : Function.Injective k:=by
    intro i j he
    apply hvi
    rw [←hk i,←hk j,he]
  have hkN (i : Fin 4) (hi : i≠0) : k i≠1:=by
    intro he
    have hpoint : v 0=v i:=by simpa only [he,one_smul] using hk i
    exact hi (hvi hpoint.symm)
  have hdist (i : Fin 4) : P.hyperbolicDist (v 0) ((k i)⁻¹ • w)=P.hyperbolicDist (v 0) w:=by
    rw [P.hyperbolicDist_inverse_smul,inv_inv,hk i]
    exact dirichlet_cycle_distance_to_center_eq P w u (hv i) (hv 0)
  have ha0 : IsAccidentalFuchsianPoint P (v 0):=
    (isAccidentalFuchsianPoint_cycle_invariant P (dirichletDomain P w) u (v 0) (hv 0)).mpr hu
  apply hwB
  apply mem_dirichletAccidentalBadCenters_of_four_circle P w hw (v 0) ha0
    ((k 1)⁻¹) ((k 2)⁻¹) ((k 3)⁻¹)
    (inv_ne_one.mpr (hkN 1 (by decide))) (inv_ne_one.mpr (hkN 2 (by decide)))
    (inv_ne_one.mpr (hkN 3 (by decide)))
    (fun he=>by have h:=hki (inv_injective he);norm_num at h)
    (fun he=>by have h:=hki (inv_injective he);norm_num at h)
    (fun he=>by have h:=hki (inv_injective he);norm_num at h)
    (P.hyperbolicDist (v 0) w) rfl (hdist 1) (hdist 2) (hdist 3)

/-- The original accidental-vertex cycle has exactly three points outside the actual null exceptional set. -/
theorem dirichlet_accidental_vertex_cycle_length_three {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (hwB : w∉dirichletAccidentalBadCenters P) (u : P.domain.carrier)
    (hu : IsAccidentalFuchsianPoint P u) (hv : IsFuchsianPolygonVertex P (dirichletDomain P w) u) :
    fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) u)=3:=by
  have hle:=dirichlet_accidental_cycle_length_le_three P w hw hwB u hu
  have hge:=(dirichletDomain_isConvexFuchsianPolygon P w hw).accidental_vertex_cycle_length_ge_three u hv hu
  omega

/-- The accidental vertex-cycle clause holds for almost every genuine original center. -/
theorem ae_dirichlet_accidental_vertex_cycleLength_eq_three {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) :
    ∀ᵐ w ∂P.area,IsDirichletCenter P w ∧
      ∀u,IsFuchsianPolygonVertex P (dirichletDomain P w) u→IsAccidentalFuchsianPoint P u→
        fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) u)=3:=by
  have hnot : ∀ᵐ w ∂P.area,w∉dirichletAccidentalBadCenters P:=
    measure_eq_zero_iff_ae_notMem.mp (dirichletAccidentalBadCenters_area_zero P)
  filter_upwards [ae_dirichlet_elliptic_cycleLength_eq_one P,hnot] with w hw hn
  exact ⟨hw.1,fun u hv hu=>dirichlet_accidental_vertex_cycle_length_three P w hw.1 hn u hu hv⟩

end LowDimensionalTopology.Geometry.Fuchsian
