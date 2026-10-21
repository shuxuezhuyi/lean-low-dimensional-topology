/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CompactifiedPolygonSides
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonLocalGeometry
public import Mathlib.Analysis.Normed.Module.Connected
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A connected set avoiding a common center forces the genuine nontrivial-intersection graph of a finite closed covering to be connected. -/
theorem finite_closed_cover_nontrivial_chains {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (K : ι→Set X) (hK : ∀i,IsClosed (K i)) (x : X) (hx : ∀i,x∈K i)
    (S : Set X) (hS : IsPreconnected S) (hxS : x∉S)
    (hcover : S⊆⋃i,K i) (hmeet : ∀i,(S∩K i).Nonempty) (i j : ι) :
    Relation.EqvGen (fun a b=>(K a∩K b).Nontrivial) i j := by
  classical
  let R:=fun a b=>(K a∩K b).Nontrivial
  let U:Set X:=⋃a:{a : ι // Relation.EqvGen R i a},K a.val
  let V:Set X:=⋃a:{a : ι // ¬Relation.EqvGen R i a},K a.val
  have hUc : IsClosed U:=isClosed_iUnion_of_finite (fun a=>hK a.val)
  have hVc : IsClosed V:=isClosed_iUnion_of_finite (fun a=>hK a.val)
  have huv : S⊆U∪V:=by
    intro z hz
    obtain ⟨a,ha⟩:=mem_iUnion.mp (hcover hz)
    by_cases he : Relation.EqvGen R i a
    · exact Or.inl (mem_iUnion.mpr ⟨⟨a,he⟩,ha⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨a,he⟩,ha⟩)
  by_contra hnot
  obtain ⟨u,huS,hui⟩:=hmeet i
  obtain ⟨v,hvS,hvj⟩:=hmeet j
  have huU : u∈U:=mem_iUnion.mpr ⟨⟨i,Relation.EqvGen.refl i⟩,hui⟩
  have hvV : v∈V:=mem_iUnion.mpr ⟨⟨j,hnot⟩,hvj⟩
  obtain ⟨z,hzS,hzU,hzV⟩:=isPreconnected_closed_iff.mp hS U V hUc hVc huv
    ⟨u,huS,huU⟩ ⟨v,hvS,hvV⟩
  obtain ⟨a,ha⟩:=mem_iUnion.mp hzU
  obtain ⟨b,hb⟩:=mem_iUnion.mp hzV
  have hxz : x≠z:=fun he=>hxS (he.symm ▸ hzS)
  have hab : R a.val b.val:=⟨x,⟨hx a.val,hx b.val⟩,z,⟨ha,hb⟩,hxz⟩
  exact b.property (Relation.EqvGen.trans _ _ _ a.property (Relation.EqvGen.rel _ _ hab))

/-- Every genuine finite family of open convex planar sets whose closures meet at zero meets one sufficiently small positive circle inside a prescribed neighborhood. -/
theorem finite_convex_family_circle_meeting {ι : Type*} [Finite ι]
    (U : ι→Set ℂ) (hc : ∀i,Convex ℝ (U i)) (ho : ∀i,IsOpen (U i))
    (hn : ∀i,(U i).Nonempty) (hz : ∀i,(0:ℂ)∈closure (U i))
    (N:Set ℂ) (hN:IsOpen N) (h0:(0:ℂ)∈N) :
    ∃r:ℝ,0<r∧Metric.sphere (0:ℂ) r⊆N∧∀k,(Metric.sphere (0:ℂ) r∩closure (U k)).Nonempty := by
  classical
  have hex (a:ι):∃z∈U a,z≠0:=by
    obtain ⟨z,hzU,hz0⟩:=(dense_compl_singleton (0:ℂ)).inter_open_nonempty (U a) (ho a) (hn a)
    exact ⟨z,hzU,hz0⟩
  choose a ha hane using hex
  obtain ⟨rN,hrN,hball⟩:=Metric.isOpen_iff.mp hN 0 h0
  have hnear : ∀ᶠr:ℝ in 𝓝[>] (0:ℝ),r<rN:=nhdsWithin_le_nhds (gt_mem_nhds hrN)
  have hbound : ∀ᶠr:ℝ in 𝓝[>] (0:ℝ),∀k,r<‖a k‖:=
    Filter.eventually_all.mpr (fun k=>nhdsWithin_le_nhds (gt_mem_nhds (norm_pos_iff.mpr (hane k))))
  have hpos : ∀ᶠr:ℝ in 𝓝[>] (0:ℝ),0<r:=self_mem_nhdsWithin
  obtain ⟨r,hr,hrN',hra⟩:=(hpos.and (hnear.and hbound)).exists
  have hs : Metric.sphere (0:ℂ) r⊆N:=fun z hz=>hball (by
    simpa only [Metric.mem_ball,Metric.mem_sphere.mp hz] using hrN')
  have hm (k:ι):(Metric.sphere (0:ℂ) r∩closure (U k)).Nonempty:=by
    let t:=r/‖a k‖
    have ht0 : 0≤t:=div_nonneg hr.le (norm_nonneg _)
    have ht1 : t≤1:=(div_le_one (norm_pos_iff.mpr (hane k))).mpr (hra k).le
    refine ⟨t•a k,?_,(hc k).closure.smul_mem_of_zero_mem (hz k) (subset_closure (ha k)) ⟨ht0,ht1⟩⟩
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    exact div_mul_cancel₀ r (norm_ne_zero_iff.mpr (hane k))
  exact ⟨r,hr,hs,hm⟩

/-- Genuine convex planar sectors covering a neighborhood of their common center have connected nontrivial-intersection graph; the needed positive circle is derived, not assumed. -/
theorem finite_convex_cover_nontrivial_chains {ι : Type*} [Finite ι]
    (U : ι→Set ℂ) (hc : ∀i,Convex ℝ (U i)) (ho : ∀i,IsOpen (U i))
    (hn : ∀i,(U i).Nonempty) (hz : ∀i,(0:ℂ)∈closure (U i))
    (N:Set ℂ) (hN:IsOpen N) (h0:(0:ℂ)∈N)
    (hcover:N⊆⋃i,closure (U i)) (i j:ι) :
    Relation.EqvGen (fun a b=>(closure (U a)∩closure (U b)).Nontrivial) i j := by
  obtain ⟨r,hr,hs,hm⟩:=finite_convex_family_circle_meeting U hc ho hn hz N hN h0
  exact finite_closed_cover_nontrivial_chains (fun k=>closure (U k)) (fun _=>isClosed_closure) 0 hz
    (Metric.sphere 0 r) (isPreconnected_sphere (by rw [Complex.rank_real_complex];norm_num) 0 r)
    (by simpa only [Metric.mem_sphere,dist_self] using hr.ne)
    (fun z hz=>hcover (hs hz)) hm i j

/-- The finite star of actual original closed polygon tiles is connected by genuine positive-length intersections through the original point. -/
theorem IsConvexFuchsianPolygon.incident_tile_nontrivial_chains {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier)
    (g k : H) (hg : x∈fuchsianDomainTile P D g) (hk : x∈fuchsianDomainTile P D k) :
    Relation.EqvGen (fun a b:H=>x∈fuchsianDomainTile P D a∧x∈fuchsianDomainTile P D b∧
      (fuchsianDomainTile P D a∩fuchsianDomainTile P D b).Nontrivial) g k := by
  classical
  let I:={a:H // x∈fuchsianDomainTile P D a}
  let : Finite I:=(hD.locallyFinite.incident_finite x).to_subtype
  let F:=normalizedPolygonKleinCoordinate P x
  have hF : Topology.IsOpenEmbedding F:=normalizedPolygonKleinCoordinate_isOpenEmbedding P x
  have hFx : F x=0:=normalizedPolygonKleinCoordinate_self P x
  let U:I→Set ℂ:=fun a=>F '' (a.val•D)
  have hDo:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hc (a:I) : Convex ℝ (U a):=by
    have he : U a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (polygonPointCoordinate P x '' (a.val•D)):=by
      rw [image_image]
      rfl
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp (hD.pointCoordinate_smul_convex x a.val)
  have ho (a:I) : IsOpen (U a):=hF.isOpenMap _ ((Homeomorph.smul a.val).isOpenMap _ hDo)
  have hn (a:I) : (U a).Nonempty:=(hDn.image (fun y=>a.val•y)).image F
  have htile (a:H) : fuchsianDomainTile P D a=closure (a•D):=(Homeomorph.smul a).image_closure D
  have hz (a:I) : (0:ℂ)∈closure (U a):=by
    rw [←hFx]
    apply image_closure_subset_closure_image hF.continuous
    exact ⟨x,(htile a.val) ▸ a.property,rfl⟩
  obtain ⟨K,_hK,hKx,_hI,hcov,_havoid⟩:=hD.locallyFinite.finite_neighborhood_star x
  obtain ⟨O,hOK,hOo,hxO⟩:=mem_nhds_iff.mp hKx
  let N:=F '' O
  have hN : IsOpen N:=hF.isOpenMap _ hOo
  have h0N : (0:ℂ)∈N:=⟨x,hxO,hFx⟩
  obtain ⟨r,hr,hs,hm⟩:=finite_convex_family_circle_meeting U hc ho hn hz N hN h0N
  let S:=F ⁻¹' Metric.sphere (0:ℂ) r
  have hsr : Metric.sphere (0:ℂ) r⊆range F:=by
    intro z hz
    obtain ⟨y,_hy,he⟩:=hs hz
    exact ⟨y,he⟩
  have hS : IsPreconnected S:=(isPreconnected_sphere
    (by rw [Complex.rank_real_complex];norm_num) (0:ℂ) r).preimage_of_isOpenMap hF.injective hF.isOpenMap hsr
  have hxS : x∉S:=by
    change F x∉Metric.sphere (0:ℂ) r
    rw [hFx]
    simpa only [Metric.mem_sphere,dist_self] using hr.ne
  have hcover : S⊆⋃a:I,fuchsianDomainTile P D a.val:=by
    intro y hy
    obtain ⟨z,hzO,hzy⟩:=hs hy
    have hey : z=y:=hF.injective hzy
    obtain ⟨a,ha,hay⟩:=mem_iUnion₂.mp (hcov (hOK (hey ▸ hzO)))
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,hay⟩
  have hmeet (a:I) : (S∩fuchsianDomainTile P D a.val).Nonempty:=by
    obtain ⟨z,hzS,hzU⟩:=hm a
    obtain ⟨y,hyz⟩:=hsr hzS
    refine ⟨y,?_,?_⟩
    · change F y∈Metric.sphere (0:ℂ) r
      rwa [hyz]
    · rw [htile,hF.isEmbedding.closure_eq_preimage_closure_image]
      change F y∈closure (U a)
      rwa [hyz]
  have hchain:=finite_closed_cover_nontrivial_chains (fun a:I=>fuchsianDomainTile P D a.val)
    (fun a=>fuchsianDomainTile_closed P D a.val) x (fun a=>a.property) S hS hxS hcover hmeet
    (⟨g,hg⟩:I) (⟨k,hk⟩:I)
  have hmap (a b:I)
      (hab:Relation.EqvGen (fun u v:I=>(fuchsianDomainTile P D u.val∩fuchsianDomainTile P D v.val).Nontrivial) a b) :
      Relation.EqvGen (fun u v:H=>x∈fuchsianDomainTile P D u∧x∈fuchsianDomainTile P D v∧
        (fuchsianDomainTile P D u∩fuchsianDomainTile P D v).Nontrivial) a.val b.val:=by
    induction hab with
    | rel a b hab => exact Relation.EqvGen.rel _ _ ⟨a.property,b.property,hab⟩
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  exact hmap _ _ hchain

/-- A literal original side-pairing step, before taking any ambient orbit relation. -/
def fuchsianSidePointStep {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (p q : P.domain.carrier) : Prop:=
  ∃s:FuchsianPolygonSides P D,p∈s.val∧q=(fuchsianSideElement hD s)⁻¹•p

/-- A genuine adjacency chain in the original point-star gives actual original side-pairing steps between its inverse-copy representatives. -/
theorem IsConvexFuchsianPolygon.incident_chain_pairing_points {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (x : P.domain.carrier) {a b:H}
    (hab:Relation.EqvGen (fun u v:H=>x∈fuchsianDomainTile P D u∧x∈fuchsianDomainTile P D v∧
      (fuchsianDomainTile P D u∩fuchsianDomainTile P D v).Nontrivial) a b) :
    Relation.EqvGen (fuchsianSidePointStep hD) (a⁻¹•x) (b⁻¹•x) := by
  induction hab with
  | rel a b hab =>
    by_cases he : a=b
    · rw [he]
      exact Relation.EqvGen.refl _
    let g:=a⁻¹*b
    have hgne : g≠1:=by
      intro hh
      apply he
      exact inv_mul_eq_one.mp hh
    have hnt : (closure D∩fuchsianDomainTile P D g).Nontrivial:=by
      have hh:=hab.2.2.image (MulAction.injective a⁻¹)
      change (a⁻¹•(a•closure D∩b•closure D)).Nontrivial at hh
      rw [smul_set_inter,inv_smul_smul,←mul_smul] at hh
      exact hh
    let s:FuchsianPolygonSides P D:=⟨closure D∩fuchsianDomainTile P D g,
      hD.side_of_nontrivial_intersection hgne hnt⟩
    have hsel : fuchsianSideElement hD s=g:=
      (hD.existsUnique_side_element s.property).unique (fuchsianSideElement_spec hD s) ⟨hgne,rfl⟩
    have hpa : a⁻¹•x∈closure D:=by
      simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using hab.1
    have hpb : b⁻¹•x∈closure D:=by
      simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using hab.2.1
    apply Relation.EqvGen.rel
    refine ⟨s,⟨hpa,?_⟩,?_⟩
    · exact ⟨b⁻¹•x,hpb,by simp only [g,mul_smul,smul_inv_smul]⟩
    · rw [hsel]
      simp only [g,mul_inv_rev,inv_inv,mul_smul,smul_inv_smul]
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- Every genuine orbit identification inside the original polygon closure is a finite chain of its actual original side pairings. -/
theorem IsConvexFuchsianPolygon.side_point_chain_of_orbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (p q : P.domain.carrier)
    (hp:p∈closure D) (hq:q∈closure D) (g:H) (hg:g•p=q) :
    Relation.EqvGen (fuchsianSidePointStep hD) p q := by
  have h1 : p∈fuchsianDomainTile P D (1:H):=by simpa only [fuchsianDomainTile,one_smul] using hp
  have hgi : p∈fuchsianDomainTile P D g⁻¹:=⟨q,hq,by
    change g⁻¹•q=p
    rw [←hg,inv_smul_smul]⟩
  have h:=hD.incident_chain_pairing_points p (hD.incident_tile_nontrivial_chains p 1 g⁻¹ h1 hgi)
  simpa only [inv_one,one_smul,inv_inv,hg] using h

/-- Literal original side-point gluing is exactly the original whole-group orbit relation on the original polygon closure. No local tessellation, evaluation injectivity, packing or generation premise is added. -/
theorem IsConvexFuchsianPolygon.side_point_chain_iff_orbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (p q : P.domain.carrier)
    (hp:p∈closure D) (hq:q∈closure D) :
    Relation.EqvGen (fuchsianSidePointStep hD) p q↔∃g:H,g•p=q := by
  constructor
  · intro h
    clear hp hq
    induction h with
    | rel a b h =>
      obtain ⟨s,_ha,he⟩:=h
      exact ⟨(fuchsianSideElement hD s)⁻¹,he.symm⟩
    | refl a => exact ⟨1,one_smul _ _⟩
    | symm a b _ ih =>
      obtain ⟨g,hg⟩:=ih
      exact ⟨g⁻¹,by rw [←hg,inv_smul_smul]⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g,hg⟩:=ih1
      obtain ⟨k,hk⟩:=ih2
      exact ⟨k*g,by rw [mul_smul,hg,hk]⟩
  · rintro ⟨g,hg⟩
    exact hD.side_point_chain_of_orbit p q hp hq g hg

end LowDimensionalTopology.Geometry.Fuchsian
