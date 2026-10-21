module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.FinitePolygonSideStars
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.StrongPolygonHalfPlaneGerms
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.SingleMirrorGroups
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Near an original proper convex corner, each actual support boundary belongs to the
corresponding original side, even if that side has further collinear marked endpoints. -/
theorem finitePolygon_vertex_local_side_facets {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n)
    (hProper : finitePolygonLine Q ((finRotate n).symm i)≠finitePolygonLine Q i) :
    ∃r : ℝ,0<r ∧ ∀p : ℍ,dist p (finitePolygonVertex Q hf i)<r →
      (p∈(finiteDiscPoincarePolygon Q hf).carrier →
        p∈(finitePolygonLine Q ((finRotate n).symm i)).carrier →
        p∈finitePolygonSide Q ((finRotate n).symm i)) ∧
      (p∈(finiteDiscPoincarePolygon Q hf).carrier →p∈(finitePolygonLine Q i).carrier →
        p∈finitePolygonSide Q i) := by
  let P:=finiteDiscPoincarePolygon Q hf
  let x:=finitePolygonPoincareVertex Q hf i
  obtain ⟨r,hr,hNear⟩:=PoincareSidePairing.exists_ball_incident_sides
    (finiteDiscPoincarePolygon_locallyFiniteSides Q hf) (finiteDiscPoincarePolygon_closedSides Q hf) x
  have hxL : finitePolygonVertex Q hf i∈(finitePolygonLine Q ((finRotate n).symm i)).carrier := by
    apply finitePolygonSide_subset_line Q _
    exact (finitePolygonVertex_side_iff Q hf i _).mpr (Or.inl rfl)
  have hxR := finitePolygonSide_subset_line Q i (finitePolygonSide_left_mem Q hf i)
  refine ⟨r,hr,?_⟩
  intro p hp
  constructor
  · intro hP hL
    have hb:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_support_line_boundary Q hQ hf ((finRotate
      n).symm i) hP hL
    obtain ⟨s,⟨j,rfl⟩,hps⟩:=mem_sUnion.mp hb
    have hxj:=hNear p hp (finitePolygonSideEquiv Q hf j) hps
    rcases (finitePolygonVertex_side_iff Q hf i j).mp hxj with hj | hj
    · simpa only [hj] using hps
    · have hpR:=finitePolygonSide_subset_line Q i (hj ▸ hps)
      have hpx:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.inter_subsingleton
        hProper) ⟨hL,hpR⟩ ⟨hxL,hxR⟩
      rw [hpx]
      exact (finitePolygonVertex_side_iff Q hf i _).mpr (Or.inl rfl)
  · intro hP hR
    have hb:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_support_line_boundary Q hQ hf i hP hR
    obtain ⟨s,⟨j,rfl⟩,hps⟩:=mem_sUnion.mp hb
    have hxj:=hNear p hp (finitePolygonSideEquiv Q hf j) hps
    rcases (finitePolygonVertex_side_iff Q hf i j).mp hxj with hj | hj
    · have hpL:=finitePolygonSide_subset_line Q _ (hj ▸ hps)
      have hpx:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.inter_subsingleton
        hProper) ⟨hpL,hR⟩ ⟨hxL,hxR⟩
      rw [hpx]
      exact finitePolygonSide_left_mem Q hf i
    · simpa only [hj] using hps

/--
Complete local local tessellation at any actual proper reciprocal-angle vertex of a weakly convex
original polygon; other original marked corners may be straight.
-/
theorem finitePolygon_weak_integral_vertex_local_condition {m : ℕ} (Q : DiscPolygon m)
    (hQ : Q.IsConvex) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (i : Fin m) (n : ℕ) (hn : 2≤n) (hangle : Q.angle i=Real.pi/(n:ℝ)) :
    ((finiteDiscPoincarePairing Q hf).project ⁻¹'
      {(finiteDiscPoincarePairing Q hf).project (1,finitePolygonPoincareVertex Q hf i)}).Finite ∧
    ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r ≤ r₀ →
      (finiteDiscPoincarePairing Q hf).LocalTessellation (1,finitePolygonPoincareVertex Q hf i) r := by
  let P:=finiteDiscPoincarePolygon Q hf
  let S:=finiteDiscPoincarePairing Q hf
  let x:=finitePolygonPoincareVertex Q hf i
  let s:=finitePolygonSideEquiv Q hf ((finRotate m).symm i)
  let t:=finitePolygonSideEquiv Q hf i
  let R:=finitePolygonPrevRay Q hf i
  let U:=finitePolygonNextRay Q hf i
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hne : Q.angle i≠Real.pi := by
    rw [hangle]
    exact (div_lt_self Real.pi_pos (by exact_mod_cast (by omega : 1<n))).ne
  have hxs : x.val∈s.val:=(finitePolygonVertex_side_iff Q hf i _).mpr (Or.inl rfl)
  have hxt : x.val∈t.val:=finitePolygonSide_left_mem Q hf i
  have hAll : ∀u : P.Side,x.val∈u.val →u=s ∨u=t := by
    intro u hu
    obtain ⟨j,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective u
    exact ((finitePolygonVertex_side_iff Q hf i j).mp hu).imp
      (congrArg (finitePolygonSideEquiv Q hf)) (congrArg (finitePolygonSideEquiv Q hf))
  have hR : S.element s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine := by
    rw [finitePolygonPrevRay_support]
    exact finiteDiscPoincarePairing_element Q hf _
  have hU : S.element t=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry U.supportLine := by
    rw [finitePolygonNextRay_support]
    exact finiteDiscPoincarePairing_element Q hf _
  have hθ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R U=Real.pi/(n:ℝ):=
    (finitePolygon_vertex_angle Q hQ hf i hne).trans hangle
  have hProper:=finitePolygon_vertex_rays_proper Q hf i hne
  have hProperL : finitePolygonLine Q ((finRotate m).symm i)≠finitePolygonLine Q i := by
    rwa [finitePolygonPrevRay_support,finitePolygonNextRay_support] at hProper
  refine ⟨S.native_integral_reflection_vertex_fiber_finite
    (finiteDiscPoincarePairing_reflection_sides Q hf) x s t hxs hxt hAll R U hR hU n hn hθ,?_⟩
  obtain ⟨rG,hrG,hG⟩:=finitePolygon_vertex_closed_angle_germ Q hQ hf i hne
  obtain ⟨rF,hrF,hF⟩:=finitePolygon_vertex_local_side_facets Q hQ hf i hProperL
  obtain ⟨rN,hrN,hNear⟩:=PoincareSidePairing.exists_ball_incident_sides
    (finiteDiscPoincarePolygon_locallyFiniteSides Q hf) (finiteDiscPoincarePolygon_closedSides Q hf) x
  let δ:=min rG (min rF rN)
  have hδ : 0<δ:=lt_min hrG (lt_min hrF hrN)
  have hGerm (z : ℍ) (hz : dist z
    x.val<δ) : z∈P.carrier ↔z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R U) :=
    hG z (hz.trans_le (min_le_left _ _))
  have hK:=S.native_incident_reflection_pair x s t hxs hxt hAll R U hR hU
  have hMem (g : S.Generated) (hg : g∈S.incidentSubgroup x) :
      g.val∈Subgroup.closure ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry U.supportLine}:Set (ℍ≃ᵢℍ)) := by
    rw [←hK]
    exact ⟨g,hg,rfl⟩
  apply S.local_radius_of_incident_chamber
    (S.native_reflection_sides_fixed (finiteDiscPoincarePairing_reflection_sides Q hf)) x δ hδ
  · intro p hp u hpu
    exact hNear p.val (hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))) u hpu
  · intro z hz
    obtain ⟨g,hg,p,hp,hpd,hgp⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_closed_angle_ball_cover R U hProper n hn hθ δ z hz
    have hgMap : g∈(S.incidentSubgroup x).map S.Generated.subtype := by rw [hK];exact hg
    obtain ⟨b,hb,hbg⟩:=hgMap
    refine ⟨b,hb,⟨p,(hGerm p hpd).mpr hp⟩,hpd,?_⟩
    change b.val p=z
    change b.val=g at hbg
    rw [hbg]
    exact hgp
  · intro g hg p q hp hq hpq
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_closed_angle_orbit_unique R U hProper n hn hθ g.val (hMem g hg)
      p.val q.val ((hGerm p.val hp).mp p.property) ((hGerm q.val hq).mp q.property) hpq
  · intro p hp g hg hfix
    have hcases:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_closed_angle_stabilizer R U hProper n hn hθ g.val (hMem g hg)
      p.val ((hGerm p.val hp).mp p.property) hfix
    rcases hcases with hvertex | hone | hMR | hMU
    · have hpx : p=x:=Subtype.ext hvertex
      rwa [hpx]
    · have hg1 : g=1:=Subtype.ext hone
      rw [hg1]
      exact (S.incidentSubgroup p).one_mem
    · have hLine : p.val∈R.supportLine.carrier := by
        apply (R.supportLine.reflection_fixed_iff p.val).mp
        change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
          R.supportLine) p.val=p.val
        rw [←hMR]
        exact hfix
      rw [finitePolygonPrevRay_support] at hLine
      have hps:=(hF p.val (hp.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).1 p.property hLine
      have hgS : g=S.generator s:=Subtype.ext (hMR.trans hR.symm)
      rw [hgS]
      exact Subgroup.subset_closure ⟨s,hps,rfl⟩
    · have hLine : p.val∈U.supportLine.carrier := by
        apply (U.supportLine.reflection_fixed_iff p.val).mp
        change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
          U.supportLine) p.val=p.val
        rw [←hMU]
        exact hfix
      rw [finitePolygonNextRay_support] at hLine
      have hpt:=(hF p.val (hp.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).2 p.property hLine
      have hgT : g=S.generator t:=Subtype.ext (hMU.trans hU.symm)
      rw [hgT]
      exact Subgroup.subset_closure ⟨t,hpt,rfl⟩

/-- Every genuine nonvertex side point of an original weakly convex finite polygon has its
actual reflected two-half-ball neighborhood; straight marked corners elsewhere are allowed. -/
theorem finitePolygon_weak_nonvertex_paired_side {n : ℕ} (Q : DiscPolygon n) (hQ : Q.IsConvex)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (x : (finiteDiscPoincarePolygon Q hf).Point) (i : Fin n)
    (hi : x.val∈finitePolygonSide Q i) (hv : x.val∉range (finitePolygonVertex Q hf)) :
    ∃r : ℝ,(finiteDiscPoincarePairing Q hf).PairedSideNeighborhood x (finitePolygonSideEquiv Q hf i) r := by
  let S:=finiteDiscPoincarePairing Q hf
  let s:=finitePolygonSideEquiv Q hf i
  let N:=finitePolygonLine Q i
  obtain ⟨m,t,hm,hLine,rG,hrG,hG⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_weak_nonvertex_halfPlane_germ Q hQ hf hi hv
  have hm0 : m≠0 := by intro h;rw [h,norm_zero] at hm;norm_num at hm
  have hl:=finitePolygonSide_subset_line Q i (finitePolygonSide_left_mem Q hf i)
  have hr:=finitePolygonSide_subset_line Q i (finitePolygonSide_right_mem Q hf i)
  obtain ⟨σ,hσ,hCut⟩:=native_halfPlane_signed_support N hm0
    ((finitePolygonVertex_injective Q hf).ne (Q.next_ne_self i).symm) hl hr
    ((hLine _).mp hl) ((hLine _).mp hr)
  obtain ⟨rN,hrN,hNear⟩:=PoincareSidePairing.exists_ball_incident_sides
    (finiteDiscPoincarePolygon_locallyFiniteSides Q hf) (finiteDiscPoincarePolygon_closedSides Q hf) x
  let r:=min rG rN
  refine ⟨r,S.pairedSideNeighborhood_of_halfPlaneReflection N (lt_min hrG hrN) hσ hi
    (finitePolygonSide_subset_line Q i) (by rfl) ?_ ?_ ?_ ?_⟩
  · intro z
    change S.element s z=N.reflection z
    rw [finiteDiscPoincarePairing_element]
    rfl
  · intro t y hy hdy
    have hxt:=hNear y (hdy.trans_le (min_le_right _ _)) t hy
    obtain ⟨j,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective t
    by_cases hji : j=i
    · exact congrArg (finitePolygonSideEquiv Q hf) hji
    · exact (hv (finitePolygon_common_sides_vertex Q hf (fun h=>hji h.symm) hi hxt)).elim
  · intro z hz
    exact (hG z (hz.trans_le (min_le_left _ _))).trans (hCut z).symm
  · intro z hz hZero
    change z∈finitePolygonSide Q i
    have hL:=(N.normalTimeAt_eq_zero_iff z).mp hZero
    have hP:=(hG z (hz.trans_le (min_le_left _ _))).mpr ((hLine z).mp hL).le
    have hB:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_support_line_boundary Q hQ hf i hP hL
    obtain ⟨s',⟨j,rfl⟩,hzj⟩:=mem_sUnion.mp hB
    have hxj:=hNear z (hz.trans_le (min_le_right _ _)) (finitePolygonSideEquiv Q hf j) hzj
    by_cases hji : j=i
    · simpa only [hji] using hzj
    · exact (hv (finitePolygon_common_sides_vertex Q hf (fun h=>hji h.symm) hi hxj)).elim

/--
At an original marked straight corner the original single mirror gives both finite whole
classes and every actual local local tessellation ball, retaining both original incident side labels.
-/
theorem finitePolygon_straight_vertex_local_condition {m : ℕ} (Q : DiscPolygon m)
    (hQ : Q.IsConvex) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (i : Fin m) (hangle : Q.angle i=Real.pi) :
    ((finiteDiscPoincarePairing Q hf).project ⁻¹'
      {(finiteDiscPoincarePairing Q hf).project (1,finitePolygonPoincareVertex Q hf i)}).Finite ∧
    ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r ≤ r₀ →
      (finiteDiscPoincarePairing Q hf).LocalTessellation (1,finitePolygonPoincareVertex Q hf i) r := by
  let P:=finiteDiscPoincarePolygon Q hf
  let S:=finiteDiscPoincarePairing Q hf
  let x:=finitePolygonPoincareVertex Q hf i
  let t:=finitePolygonSideEquiv Q hf i
  let N:=finitePolygonLine Q i
  let K:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry N}:Set
    (ℍ≃ᵢℍ))
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  obtain ⟨hSame,m₀,t₀,hm₀,hLine,rG,hrG,hG⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_straight_halfPlane_germ Q hQ hf i hangle
  have hAllMirror (u : P.Side) (hu : x.val∈u.val) :
      S.element u=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry N := by
    obtain ⟨j,rfl⟩:=(finitePolygonSideEquiv Q hf).surjective u
    rw [finiteDiscPoincarePairing_element]
    rcases (finitePolygonVertex_side_iff Q hf i j).mp hu with hj | hj
    · rw [hj,hSame]
    · rw [hj]
  have hK : Finite K:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_single_mirror_group N).2
  let : Finite K:=hK
  let : Finite (S.incidentSubgroup x):=S.finite_incidentSubgroup_of_finite_ambient x K (by
    intro u hu
    rw [hAllMirror u hu]
    exact Subgroup.subset_closure rfl)
  have hLe : S.incidentSubgroup x≤K.comap S.Generated.subtype := by
    change Subgroup.closure _≤K.comap S.Generated.subtype
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨u,hu,rfl⟩
    change S.element u∈K
    rw [hAllMirror u hu]
    exact Subgroup.subset_closure rfl
  have hCase (g : S.Generated) (hg : g∈S.incidentSubgroup x) :
      g.val=1 ∨g.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry N :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_single_mirror_group N).1 g.val (hLe hg)
  have hSelf:=S.native_reflection_sides_fixed (finiteDiscPoincarePairing_reflection_sides Q hf)
  refine ⟨S.finite_project_fiber_of_finite_incidentSubgroup hSelf x,?_⟩
  have hm0 : m₀≠0 := by intro h;rw [h,norm_zero] at hm₀;norm_num at hm₀
  have hl:=finitePolygonSide_subset_line Q i (finitePolygonSide_left_mem Q hf i)
  have hr:=finitePolygonSide_subset_line Q i (finitePolygonSide_right_mem Q hf i)
  obtain ⟨σ,hσ,hCut⟩:=native_halfPlane_signed_support N hm0
    ((finitePolygonVertex_injective Q hf).ne (Q.next_ne_self i).symm) hl hr
    ((hLine _).mp hl) ((hLine _).mp hr)
  obtain ⟨rN,hrN,hNear⟩:=PoincareSidePairing.exists_ball_incident_sides
    (finiteDiscPoincarePolygon_locallyFiniteSides Q hf) (finiteDiscPoincarePolygon_closedSides Q hf) x
  let δ:=min rG rN
  have hδ : 0<δ:=lt_min hrG hrN
  have hGerm (z : ℍ) (hz : dist z x.val<δ) : z∈P.carrier ↔0≤σ*N.normalTimeAt z :=
    (hG z (hz.trans_le (min_le_left _ _))).trans (hCut z).symm
  have hxt : x.val∈t.val:=finitePolygonSide_left_mem Q hf i
  have hTx (z : ℍ) : S.generator t •z=N.reflection z := by
    change S.element t z=N.reflection z
    rw [finiteDiscPoincarePairing_element]
    rfl
  have hTxmem : S.generator t∈S.incidentSubgroup x:=Subgroup.subset_closure ⟨t,hxt,rfl⟩
  have hNx : N.reflection x.val=x.val:=(N.reflection_fixed_iff x.val).mpr hl
  have hDist (z : ℍ) : dist (N.reflection z) x.val=dist z x.val := by
    calc
      dist (N.reflection z) x.val=dist (N.reflection z) (N.reflection x.val) := by rw [hNx]
      _=dist z x.val:=N.reflection_isometry.dist_eq z x.val
  apply S.local_radius_of_incident_chamber hSelf x δ hδ
  · intro p hp u hpu
    exact hNear p.val (hp.trans_le (min_le_right _ _)) u hpu
  · intro z hz
    by_cases hpos : 0≤σ*N.normalTimeAt z
    · refine ⟨1,(S.incidentSubgroup x).one_mem,⟨z,(hGerm z hz).mpr hpos⟩,hz,?_⟩
      exact one_smul _ _
    · have hd : dist (N.reflection z) x.val<δ:=by rwa [hDist]
      have hposR : 0≤σ*N.normalTimeAt (N.reflection z) := by
        rw [N.normalTimeAt_self_reflection,mul_neg]
        linarith
      refine ⟨S.generator t,hTxmem,⟨N.reflection z,(hGerm _ hd).mpr hposR⟩,hd,?_⟩
      rw [hTx]
      exact N.reflection_involutive z
  · intro g hg p q hp hq hpq
    rcases hCase g hg with hone | hmirror
    · change g.val p.val=q.val at hpq
      rw [hone] at hpq
      exact hpq
    · have hpt:=(hGerm p.val hp).mp p.property
      have hqt:=(hGerm q.val hq).mp q.property
      have hqTime : N.normalTimeAt q.val= -N.normalTimeAt p.val := by
        rw [←hpq]
        change N.normalTimeAt (g.val p.val)= -N.normalTimeAt p.val
        rw [hmirror]
        exact N.normalTimeAt_self_reflection p.val
      rw [hqTime,mul_neg] at hqt
      have hzero : N.normalTimeAt p.val=0 :=
        (mul_eq_zero.mp (by linarith : σ*N.normalTimeAt p.val=0)).resolve_left hσ
      have hpf : N.reflection p.val=p.val :=
        (N.reflection_fixed_iff p.val).mpr ((N.normalTimeAt_eq_zero_iff p.val).mp hzero)
      change g.val p.val=q.val at hpq
      rw [hmirror] at hpq
      exact hpf.symm.trans hpq
  · intro p hp g hg hfix
    rcases hCase g hg with hone | hmirror
    · have hg1 : g=1:=Subtype.ext hone
      rw [hg1]
      exact (S.incidentSubgroup p).one_mem
    · have hLineP : p.val∈N.carrier := by
        apply (N.reflection_fixed_iff p.val).mp
        change g.val p.val=p.val at hfix
        rwa [hmirror] at hfix
      have hB:=_root_.LowDimensionalTopology.Geometry.Fuchsian.finitePolygon_support_line_boundary Q hQ hf i p.property hLineP
      obtain ⟨u,hu,hpu⟩:=mem_sUnion.mp hB
      let uSide : P.Side:=⟨u,hu⟩
      have hxU:=hNear p.val (hp.trans_le (min_le_right _ _)) uSide hpu
      have hgU : g=S.generator uSide:=Subtype.ext (hmirror.trans (hAllMirror uSide hxU).symm)
      rw [hgU]
      exact Subgroup.subset_closure ⟨uSide,hpu,rfl⟩

/--
All actual points of the original finite reciprocal-angle polygon satisfy local local tessellation,
including its genuine marked angle-pi vertices and both original incident side labels.
-/
theorem finitePolygon_positive_integral_local_tessellation {m : ℕ} (Q : DiscPolygon m)
    (hQ : Q.IsConvex) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (n : Fin m→ℕ) (hn : ∀i,1≤n i) (hangle : ∀i,Q.angle i=Real.pi/(n i:ℝ)) :
    (finiteDiscPoincarePairing Q hf).FiniteFiberLocalTessellationCondition := by
  let P:=finiteDiscPoincarePolygon Q hf
  let S:=finiteDiscPoincarePairing Q hf
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hVertices (i : Fin m) :
      (S.project ⁻¹' {S.project (1,finitePolygonPoincareVertex Q hf i)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r ≤ r₀ →
        S.LocalTessellation (1,finitePolygonPoincareVertex Q hf i) r := by
    by_cases hi : n i=1
    · apply finitePolygon_straight_vertex_local_condition Q hQ hf i
      simpa only [hi,Nat.cast_one,div_one] using hangle i
    · exact finitePolygon_weak_integral_vertex_local_condition Q hQ hf i (n i)
        (by have:=hn i;omega) (hangle i)
  have hcases (x : P.Point) : x.val∈P.interior ∨
      (∃i,x=finitePolygonPoincareVertex Q hf i) ∨
      ∃s : P.Side,∃r : ℝ,S.PairedSideNeighborhood x s r := by
    by_cases hxI : x.val∈P.interior
    · exact Or.inl hxI
    right
    by_cases hxV : x.val∈range (finitePolygonVertex Q hf)
    · obtain ⟨i,hi⟩:=hxV
      exact Or.inl ⟨i,Subtype.ext hi.symm⟩
    · right
      have hxB : x.val∈P.boundary:=x.prop.resolve_left hxI
      obtain ⟨s,⟨i,rfl⟩,hxs⟩:=mem_sUnion.mp hxB
      obtain ⟨r,hr⟩:=finitePolygon_weak_nonvertex_paired_side Q hQ hf x i hxs hxV
      exact ⟨finitePolygonSideEquiv Q hf i,r,hr⟩
  constructor
  · intro x
    rcases hcases x with hx | ⟨i,rfl⟩ | ⟨s,r,hr⟩
    · rw [S.project_fiber_eq_singleton_of_interior (1,x) hx]
      exact finite_singleton _
    · exact (hVertices i).1
    · exact hr.finite_class S
  · intro x
    rcases hcases x with hx | ⟨i,rfl⟩ | ⟨s,r,hr⟩
    · exact S.interior_local_radius (finiteDiscPoincarePolygon_interior_isOpen Q hf) x hx
    · exact (hVertices i).2
    · exact hr.local_radius S

/-- The original finite weakly convex polygon with positive-integer reciprocal angles,
including straight marked corners, is a true fundamental domain of its actual discrete reflection group. -/
theorem finitePolygon_positive_integral_poincare {m : ℕ} (Q : DiscPolygon m)
    (hQ : Q.IsConvex) (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (n : Fin m→ℕ) (hn : ∀i,1≤n i) (hangle : ∀i,Q.angle i=Real.pi/(n i:ℝ)) :
    DiscreteTopology (↥(Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))
      ℍ MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior) := by
  have hh:=(finiteDiscPoincarePairing Q hf).native_poincare_of_compact
    (finitePolygon_positive_integral_local_tessellation Q hQ hf n hn hangle)
    (finiteDiscPoincarePolygon_interior_isOpen Q hf)
    (finiteDiscPoincarePolygon_interior_isConnected Q hf)
    (finiteDiscPoincarePolygon_carrier Q hf)
    (finiteDiscPoincarePolygon_isCompact Q hf)
    (finiteDiscPoincarePolygon_countableSides Q hf)
    (finiteDiscPoincarePolygon_geodesicSides Q hf)
  change DiscreteTopology (↥(finiteDiscPoincarePairing Q hf).Generated) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (finiteDiscPoincarePairing Q
      hf).Generated
      ℍ MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior) at hh
  rwa [finiteDiscPoincarePairing_generated Q hf] at hh

/--
The literal original polygon and its true positive-integer reciprocal angles
alone imply discreteness of its actual original side-reflection group and its given fundamental domain.
-/
theorem polygon_reflection_group_discrete_and_isFundamentalDomain {m : ℕ} (Q : DiscPolygon m)
    (n : Fin m→ℕ) (hn : ∀i,1≤n i) (hangle : ∀i,Q.angle i=Real.pi/(n i:ℝ)) :
    DiscreteTopology (↥(Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (Subgroup.closure
      (range (fun i : Fin m=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry
        (finitePolygonLine Q i))))
      ℍ MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior) := by
  have ha : ∀i,Q.angle i≤Real.pi := by
    intro i
    rw [hangle i]
    exact div_le_self Real.pi_pos.le (by exact_mod_cast hn i)
  have hf : ∀i,‖(Q.vertices i : ℂ)‖<1 := by
    intro i
    apply Q.vertex_finite_of_angle_pos i
    rw [hangle i]
    apply div_pos Real.pi_pos
    exact_mod_cast (by have:=hn i;omega : 0<n i)
  have hQ : Q.IsConvex:=Q.isConvex_iff_angles_le_pi.mpr ha
  exact finitePolygon_positive_integral_poincare Q hQ hf n hn hangle

end LowDimensionalTopology.Geometry.Polygon
