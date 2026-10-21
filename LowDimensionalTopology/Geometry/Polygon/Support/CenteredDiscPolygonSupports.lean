/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonAngularOrder
public import Mathlib.Analysis.Convex.GaugeRescale
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicNormalCoordinates
/-! # Genuine Jordan polygons from supports about an arbitrary interior point

The supplied data consist of actual cyclic vertices, actual supporting half-planes,
and a strictly feasible center. Their intersection lies in the closed Klein disc.
There is no origin-position, angle, Jordan-boundary, triangulation or area hypothesis.
Actual simple edges, Jordan boundary, interior, convexity and numeric corner angles
are proved, with finite and ideal vertices treated together.
-/
@[expose] public section
open Set Filter InnerProductGeometry
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

theorem complex_affine_hyperplane_line (n p q x : ℂ) (t : ℝ)
    (hn : ‖n‖=1) (hpq : p≠q) (hp : inner ℝ n p=t) (hq : inner ℝ n q=t)
    (hx : inner ℝ n x=t) : ∃ s : ℝ,x=(1-s) • p+s • q := by
  let v := q-p
  let w := x-p
  have hv : v≠0 := sub_ne_zero.mpr hpq.symm
  have hk : ‖v‖^2≠0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  have hnv : inner ℝ n v=0 := by
    change inner ℝ n (q-p)=0
    rw [inner_sub_right,hq,hp,sub_self]
  have hnw : inner ℝ w n=0 := by
    rw [real_inner_comm n w]
    change inner ℝ n (x-p)=0
    rw [inner_sub_right,hx,hp,sub_self]
  have hg := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_gram_three n v w
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hn,one_pow,hnv,hnw] at hg
  let s := inner ℝ v w/‖v‖^2
  have hd : ‖w-s • v‖^2=0 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right,
      real_inner_comm v w]
    dsimp [s]
    field_simp [hk]
    change ‖w‖^2*‖v‖^2 - 2*(inner ℝ v w)^2 + (inner ℝ v w)^2=‖v‖^2*0
    nlinarith only [hg]
  have he := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hd))
  refine ⟨s,?_⟩
  change x-p=s • (q-p) at he
  calc
    x = p+s • (q-p) := by rw [← he];abel
    _ = (1-s) • p+s • q := by module

structure CenteredDiscPolygonSupportData (n : ℕ) where
  three_le : 3≤n
  vertices : Fin n → 𝕔𝔻
  vertices_injective : Function.Injective vertices
  normals : Fin n → ℂ
  normal_norm : ∀ i,‖normals i‖=1
  offsets : Fin n → ℝ
  center : ℂ
  center_strict : ∀ i,inner ℝ (normals i) center<offsets i
  incident : ∀ i,inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices
    i))=offsets i ∧
    inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices (finRotate n
      i)))=offsets i
  nonincident : ∀ i j,j≠i → j≠finRotate n i →
    inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices j))<offsets i
  region_subset_closedBall : {z : ℂ | ∀ i,inner ℝ (normals i) z≤offsets i} ⊆ Metric.closedBall 0 1

theorem centeredPolygonSupport_next_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hi : i = Fin.last k
  · subst i
    rw [finRotate_last]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero,Fin.val_last] at hv
    omega
  · have hv : ((finRotate (k+1)) i).val = i.val+1 := coe_finRotate_of_ne_last hi
    intro he
    exact Nat.succ_ne_self i.val (hv.symm.trans (congrArg Fin.val he))

theorem centeredPolygonSupport_next_next_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  intro he
  have hi := i.isLt
  have hr := (finRotate n i).isLt
  by_cases hlast : i.val+1 = n
  · have hzero := polygon_finRotate_val_of_last i hlast
    have hsucc := polygon_finRotate_val_of_succ_lt (finRotate n i) (by omega)
    have heval := congrArg Fin.val he
    omega
  · have hsucc := polygon_finRotate_val_of_succ_lt i (by omega)
    by_cases hlast' : (finRotate n i).val+1 = n
    · have hzero := polygon_finRotate_val_of_last (finRotate n i) hlast'
      have heval := congrArg Fin.val he
      omega
    · have hsucc' := polygon_finRotate_val_of_succ_lt (finRotate n i) (by omega)
      have heval := congrArg Fin.val he
      omega

def CenteredDiscPolygonSupportData.kleinRegion {n : ℕ} (S : CenteredDiscPolygonSupportData n) : Set ℂ :=
  {z | ∀ i,inner ℝ (S.normals i) z ≤ (S.offsets i)}

def CenteredDiscPolygonSupportData.strictKleinRegion {n : ℕ} (S : CenteredDiscPolygonSupportData n) : Set ℂ :=
  {z | ∀ i,inner ℝ (S.normals i) z < (S.offsets i)}

theorem CenteredDiscPolygonSupportData.kleinRegion_isClosed {n : ℕ} (S : CenteredDiscPolygonSupportData n) : IsClosed S.kleinRegion := by
  have he : S.kleinRegion = ⋂ i,{z : ℂ | inner ℝ (S.normals i) z ≤ (S.offsets i)} := by ext z; simp [CenteredDiscPolygonSupportData.kleinRegion]
  rw [he]
  exact isClosed_iInter (fun i => isClosed_le (continuous_const.inner continuous_id) continuous_const)

theorem CenteredDiscPolygonSupportData.kleinRegion_convex {n : ℕ} (S : CenteredDiscPolygonSupportData n) : Convex ℝ S.kleinRegion := by
  have he : S.kleinRegion = ⋂ i,{z : ℂ | inner ℝ (S.normals i) z ≤ (S.offsets i)} := by ext z; simp [CenteredDiscPolygonSupportData.kleinRegion]
  rw [he]
  exact convex_iInter (fun i => convex_halfSpace_le (innerSL ℝ (S.normals i)).toLinearMap.isLinear (S.offsets i))

theorem CenteredDiscPolygonSupportData.kleinRegion_isCompact {n : ℕ} (S : CenteredDiscPolygonSupportData
  n) : IsCompact S.kleinRegion :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset S.kleinRegion_isClosed S.region_subset_closedBall

theorem CenteredDiscPolygonSupportData.strictKleinRegion_isOpen {n : ℕ} (S : CenteredDiscPolygonSupportData n) : IsOpen S.strictKleinRegion := by
  have he : S.strictKleinRegion = ⋂ i,{z : ℂ | inner ℝ (S.normals i) z < (S.offsets i)} := by ext z; simp [CenteredDiscPolygonSupportData.strictKleinRegion]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_const.inner continuous_id) continuous_const)

theorem CenteredDiscPolygonSupportData.strictKleinRegion_subset {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    S.strictKleinRegion ⊆ S.kleinRegion := fun _ hz i => (hz i).le

theorem CenteredDiscPolygonSupportData.strict_subset_interior {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    S.strictKleinRegion ⊆ interior S.kleinRegion :=
  interior_maximal S.strictKleinRegion_subset S.strictKleinRegion_isOpen

theorem CenteredDiscPolygonSupportData.interior_subset_strict {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    interior S.kleinRegion ⊆ S.strictKleinRegion := by
  intro z hz i
  have hzi := (interior_subset hz) i
  apply lt_of_le_of_ne hzi
  intro he
  obtain ⟨ε,hε,hsub⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let w := z + (ε/2) • S.normals i
  have hw : w ∈ Metric.ball z ε := by
    change dist (z+(ε/2) • S.normals i) z < ε
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < ε/2),
      S.normal_norm i,mul_one]
    linarith only [hε]
  have hwi := (interior_subset (hsub hw)) i
  change inner ℝ (S.normals i) (z+(ε/2) • S.normals i) ≤ (S.offsets i) at hwi
  rw [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,S.normal_norm i,one_pow,mul_one,he] at hwi
  linarith only [hwi,hε]

theorem CenteredDiscPolygonSupportData.interior_kleinRegion {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    interior S.kleinRegion = S.strictKleinRegion :=
  subset_antisymm S.interior_subset_strict S.strict_subset_interior

theorem CenteredDiscPolygonSupportData.center_mem_strict {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    S.center ∈ S.strictKleinRegion := S.center_strict

theorem CenteredDiscPolygonSupportData.kleinRegion_interior_nonempty {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    (interior S.kleinRegion).Nonempty := ⟨S.center,S.strict_subset_interior S.center_mem_strict⟩

theorem CenteredDiscPolygonSupportData.vertex_mem_region {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i) ∈ S.kleinRegion := by
  intro j
  by_cases hij : i = j
  · subst i
    exact (S.incident j).1.le
  · by_cases hij' : i = finRotate n j
    · subst i
      exact (S.incident j).2.le
    · exact (S.nonincident j i hij hij').le

theorem CenteredDiscPolygonSupportData.closure_strictKleinRegion {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    closure S.strictKleinRegion = S.kleinRegion := by
  rw [← S.interior_kleinRegion]
  exact (S.kleinRegion_convex.closure_interior_eq_closure_of_nonempty_interior
    S.kleinRegion_interior_nonempty).trans S.kleinRegion_isClosed.closure_eq

theorem CenteredDiscPolygonSupportData.frontier_jordan {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    Nonempty (↥(frontier S.kleinRegion) ≃ₜ Metric.sphere (0 : ℝ × ℝ) 1) := by
  let e : ℂ ≃L[ℝ] ℝ × ℝ := Complex.equivRealProdCLM
  let A : Set (ℝ × ℝ) := e '' S.kleinRegion
  have hc : Convex ℝ A := S.kleinRegion_convex.linear_image e.toLinearEquiv.toLinearMap
  have hne : (interior A).Nonempty := by
    change (interior (e.toHomeomorph '' S.kleinRegion)).Nonempty
    rw [← e.toHomeomorph.image_interior]
    exact S.kleinRegion_interior_nonempty.image e
  have hk : IsCompact A := S.kleinRegion_isCompact.image e.continuous
  obtain ⟨h,_,_,hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hk.isBounded
  exact ⟨((e.toHomeomorph.isEmbedding.homeomorphImage (frontier S.kleinRegion)).trans
    (Homeomorph.setCongr (e.toHomeomorph.image_frontier S.kleinRegion))).trans
    ((h.isEmbedding.homeomorphImage (frontier A)).trans (Homeomorph.setCongr hf))⟩

theorem CenteredDiscPolygonSupportData.exterior_isPreconnected {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    IsPreconnected S.kleinRegionᶜ := by
  obtain ⟨h,_,hc,_⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    S.kleinRegion_convex S.kleinRegion_interior_nonempty S.kleinRegion_isCompact.isBounded
  rw [S.kleinRegion_isClosed.closure_eq] at hc
  have he : h.symm '' (Metric.closedBall (0 : ℂ) 1)ᶜ = S.kleinRegionᶜ := by
    rw [← hc,← h.image_compl]
    simp only [Set.image_image,h.symm_apply_apply,Set.image_id']
  rw [← he]
  have hs : IsPreconnected ((Metric.closedBall (0 : ℂ) 1)ᶜ) := by
    simpa only [Metric.closedBall,dist_zero_right,Set.compl_ofPred,not_le] using
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_outer_region_isPreconnected (by norm_num : (0 : ℝ) ≤ 1))
  exact hs.image h.symm h.symm.continuous.continuousOn

def CenteredDiscPolygonSupportData.kleinFace {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) : Set ℂ :=
  {z | z ∈ S.kleinRegion ∧ inner ℝ (S.normals i) z = S.offsets i}

theorem CenteredDiscPolygonSupportData.frontier_eq_faces {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    frontier S.kleinRegion = ⋃ i,S.kleinFace i := by
  classical
  rw [frontier,S.kleinRegion_isClosed.closure_eq,S.interior_kleinRegion]
  ext z
  simp only [Set.mem_sdiff,mem_iUnion,CenteredDiscPolygonSupportData.kleinFace,mem_ofPred_eq,CenteredDiscPolygonSupportData.strictKleinRegion]
  constructor
  · rintro ⟨hz,hnot⟩
    obtain ⟨i,hi⟩ := not_forall.mp hnot
    exact ⟨i,hz,le_antisymm (hz i) (not_lt.mp hi)⟩
  · rintro ⟨i,hz,hi⟩
    exact ⟨hz,fun hs => (ne_of_lt (hs i)) hi⟩

theorem CenteredDiscPolygonSupportData.segment_subset_face {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) ⊆ S.kleinFace i := by
  rintro z ⟨a,b,ha,hb,hab,rfl⟩
  constructor
  · exact S.kleinRegion_convex (S.vertex_mem_region i) (S.vertex_mem_region (finRotate n i)) ha hb hab
  · rw [inner_add_right,real_inner_smul_right,real_inner_smul_right,(S.incident i).1,(S.incident i).2]
    rw [← add_mul,hab,one_mul]

theorem CenteredDiscPolygonSupportData.face_subset_segment {n : ℕ}
    (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    S.kleinFace i ⊆ segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) := by
  intro z hz
  have hpq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i) ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i)) := by
    intro he
    exact centeredPolygonSupport_next_ne_self S.three_le i
      (S.vertices_injective (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he)).symm
  obtain ⟨s,hs⟩ := complex_affine_hyperplane_line (S.normals i)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
      i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) z
    (S.offsets i) (S.normal_norm i) hpq (S.incident i).1 (S.incident i).2 hz.2
  let prev := (finRotate n).symm i
  have hprev : finRotate n prev=i := (finRotate n).apply_symm_apply i
  have hpi : prev≠i := by
    intro he
    exact centeredPolygonSupport_next_ne_self S.three_le i (he ▸ hprev)
  have hpnext : finRotate n i≠prev := by
    intro he
    have hh := congrArg (finRotate n) he
    rw [hprev] at hh
    exact centeredPolygonSupport_next_next_ne_self S.three_le i hh
  have hprevp : inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))=S.offsets prev := by
    simpa only [hprev] using (S.incident prev).2
  have hprevq := S.nonincident prev (finRotate n i) hpnext
    (by rw [hprev];exact centeredPolygonSupport_next_ne_self S.three_le i)
  have hs0 : 0≤s := by
    have h := hz.1 prev
    rw [hs,inner_add_right,real_inner_smul_right,real_inner_smul_right,hprevp] at h
    by_contra hh
    have hprod := mul_pos_of_neg_of_neg (lt_of_not_ge hh) (sub_neg.mpr hprevq)
    nlinarith only [h,hprod]
  have hnext := centeredPolygonSupport_next_ne_self S.three_le i
  have hnextp := S.nonincident (finRotate n i) i hnext.symm
    (centeredPolygonSupport_next_next_ne_self S.three_le i).symm
  have hnextq := (S.incident (finRotate n i)).1
  have hs1 : s≤1 := by
    have h := hz.1 (finRotate n i)
    rw [hs,inner_add_right,real_inner_smul_right,real_inner_smul_right,hnextq] at h
    by_contra hh
    have hprod := mul_pos_of_neg_of_neg (by linarith [lt_of_not_ge hh] : 1-s<0)
      (sub_neg.mpr hnextp)
    nlinarith only [h,hprod]
  exact ⟨1-s,s,sub_nonneg.mpr hs1,hs0,by ring,hs.symm⟩

theorem CenteredDiscPolygonSupportData.face_eq_segment {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    S.kleinFace i = segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) :=
  subset_antisymm (S.face_subset_segment i) (S.segment_subset_face i)

theorem CenteredDiscPolygonSupportData.face_inter_subset_endpoints {n : ℕ} (S : CenteredDiscPolygonSupportData n)
    {i j : Fin n} (hij : i ≠ j) :
    S.kleinFace i ∩ S.kleinFace j ⊆
      {_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i),_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))} := by
  rintro z ⟨hi,hj⟩
  obtain ⟨a,b,ha,hb,hab,he⟩ := S.face_eq_segment i ▸ hi
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith only [hab,ha0]
    exact Or.inr (by simpa only [ha0,hb1,zero_smul,one_smul,zero_add,mem_singleton_iff] using he.symm)
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith only [hab,hb0]
    exact Or.inl (by simpa only [ha1,hb0,zero_smul,one_smul,add_zero] using he.symm)
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hleft := (S.vertex_mem_region i) j
  have hright := (S.vertex_mem_region (finRotate n i)) j
  have hstrict : inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    (S.vertices i)) < S.offsets j ∨
      inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) < S.offsets j := by
    by_cases hinext : i = finRotate n j
    · right
      refine S.nonincident j (finRotate n i) ?_ ?_
      · intro hh
        rw [hinext] at hh
        exact centeredPolygonSupport_next_next_ne_self S.three_le j hh
      · intro hh
        exact centeredPolygonSupport_next_ne_self S.three_le i (hh.trans hinext.symm)
    · exact Or.inl (S.nonincident j i hij hinext)
  have hweighted : inner ℝ (S.normals j) (a • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    (S.vertices i) +
      b • _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) < S.offsets j := by
    rw [inner_add_right,real_inner_smul_right,real_inner_smul_right]
    rcases hstrict with hl | hr
    · calc
        _ < a*S.offsets j + b*S.offsets j := add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hl ha') (mul_le_mul_of_nonneg_left hright hb)
        _ = S.offsets j := by rw [← add_mul,hab,one_mul]
    · calc
        _ < a*S.offsets j + b*S.offsets j := add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_left hleft ha) (mul_lt_mul_of_pos_left hr hb')
        _ = S.offsets j := by rw [← add_mul,hab,one_mul]
  rw [he,hj.2] at hweighted
  exact (lt_irrefl _ hweighted).elim

theorem CenteredDiscPolygonSupportData.edge_image_eq_face {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' discPolygonEdge S.vertices i = S.kleinFace i := by
  rw [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,←
    S.face_eq_segment i]

theorem CenteredDiscPolygonSupportData.boundary_image_eq_frontier {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' discPolygonBoundary S.vertices = frontier S.kleinRegion := by
  rw [discPolygonBoundary,Set.image_iUnion,S.frontier_eq_faces]
  exact iUnion_congr S.edge_image_eq_face

theorem CenteredDiscPolygonSupportData.simple_edges {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    ∀ i j : Fin n,i ≠ j → discPolygonEdge S.vertices i ∩ discPolygonEdge S.vertices j ⊆
      {S.vertices i,S.vertices (finRotate n i)} ∩ {S.vertices j,S.vertices (finRotate n j)} := by
  intro i j hij p hp
  have hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ S.kleinFace i := S.edge_image_eq_face i ▸ mem_image_of_mem _ hp.1
  have hj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ S.kleinFace j := S.edge_image_eq_face j ▸ mem_image_of_mem _ hp.2
  constructor
  · rcases S.face_inter_subset_endpoints hij ⟨hi,hj⟩ with he | he
    · exact Or.inl (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he)
    · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he)
  · rcases S.face_inter_subset_endpoints hij.symm ⟨hj,hi⟩ with he | he
    · exact Or.inl (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he)
    · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he)

def CenteredDiscPolygonSupportData.toDiscPolygon {n : ℕ} (S : CenteredDiscPolygonSupportData n) : DiscPolygon n where
  three_le := S.three_le
  vertices := S.vertices
  vertices_injective := S.vertices_injective
  simple_edges := S.simple_edges
  jordanBoundary := by
    obtain ⟨h⟩ := S.frontier_jordan
    exact ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.homeomorphImage
      (discPolygonBoundary S.vertices)).trans ((Homeomorph.setCongr S.boundary_image_eq_frontier).trans h)⟩

theorem CenteredDiscPolygonSupportData.complexBoundary_image {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' S.toDiscPolygon.complexBoundary = frontier S.kleinRegion := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) ''
    discPolygonBoundary S.vertices) = _
  rw [Set.image_image]
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed] using S.boundary_image_eq_frontier

theorem CenteredDiscPolygonSupportData.complexOutside_image {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' S.toDiscPolygon.complexOutside = S.kleinRegionᶜ := by
  have hx : (2 : ℂ) ∈ S.toDiscPolygon.complexBoundaryᶜ := by
    intro hx
    obtain ⟨p,_,hp⟩ := hx
    have hn := p.norm_le_one
    rw [hp] at hn
    norm_num at hn
  have htwo : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph (2 : ℂ) = 2 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinFormula (2 : ℂ) = 2
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinFormula,ite_eq_right (by norm_num)]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' connectedComponentIn S.toDiscPolygon.complexBoundaryᶜ (2 : ℂ) = _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_connectedComponentIn
    hx,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_compl,
    S.complexBoundary_image,htwo]
  have hcl : closure (interior S.kleinRegion) = S.kleinRegion := by
    rw [S.interior_kleinRegion,S.closure_strictKleinRegion]
  have hfr : frontier (interior S.kleinRegion) = frontier S.kleinRegion := by
    rw [frontier,hcl,isOpen_interior.interior_eq,frontier,S.kleinRegion_isClosed.closure_eq]
  calc
    _ = connectedComponentIn (frontier (interior S.kleinRegion))ᶜ (2 : ℂ) := by rw [hfr]
    _ = (closure (interior S.kleinRegion))ᶜ := by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.connectedComponentIn_compl_frontier_of_mem_exterior isOpen_interior
      · rw [hcl]
        exact S.exterior_isPreconnected
      · rw [hcl]
        intro h
        have hn := S.region_subset_closedBall h
        norm_num at hn
    _ = S.kleinRegionᶜ := by rw [hcl]

theorem CenteredDiscPolygonSupportData.complexInterior_image {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' S.toDiscPolygon.complexInterior = S.strictKleinRegion := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' (S.toDiscPolygon.complexBoundaryᶜ \
    S.toDiscPolygon.complexOutside) = _
  rw [Set.image_sdiff _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.injective,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_compl,S.complexBoundary_image,
    S.complexOutside_image,frontier,S.kleinRegion_isClosed.closure_eq,S.interior_kleinRegion]
  ext z
  simp only [Set.mem_sdiff,mem_compl_iff,not_and,not_not]
  constructor
  · rintro ⟨h,hz⟩
    exact h hz
  · intro hz
    exact ⟨fun _ => hz,S.strictKleinRegion_subset hz⟩

theorem CenteredDiscPolygonSupportData.toDiscPolygon_interior {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    S.toDiscPolygon.interior = {z : 𝔻 | ∀ i,inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) < S.offsets i} := by
  have he : S.toDiscPolygon.complexInterior = _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph ⁻¹' S.strictKleinRegion := by
    rw [← S.complexInterior_image,Set.preimage_image_eq _
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.injective]
  ext z
  change (z : ℂ) ∈ S.toDiscPolygon.complexInterior ↔ _
  rw [he]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph (z : ℂ) ∈ S.strictKleinRegion ↔ _
  rw [← show ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z : 𝕔𝔻) : ℂ) = (z : ℂ) from rfl,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
  rfl

theorem CenteredDiscPolygonSupportData.toDiscPolygon_isConvex {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    S.toDiscPolygon.IsConvex := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S.toDiscPolygon.interior
  rw [S.toDiscPolygon_interior]
  have he : {z : 𝔻 | ∀ i,inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) <
    S.offsets i} =
      ⋂ i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt (S.normals i) (S.offsets i) := by ext z; simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt]
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.iInter (fun i =>
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt_hConvex (S.normals i) (S.offsets i))

theorem CenteredDiscPolygonSupportData.closedModelClosure_image {n : ℕ} (S : CenteredDiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S.toDiscPolygon.interior = S.kleinRegion := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,← _root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.closure_image_eq,Set.image_image]
  have he : (fun x : 𝔻 => _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel x)) '' S.toDiscPolygon.interior =
      S.strictKleinRegion := by
    rw [← S.complexInterior_image,← S.toDiscPolygon.interior_complex_image,Set.image_image]
    congr 1
    funext z
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z)).symm
  rw [he,S.closure_strictKleinRegion]

def CenteredDiscPolygonSupportData.supportLine {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin
  n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (S.vertices i) (S.vertices
    (finRotate n i))
    (S.vertices_injective.ne (centeredPolygonSupport_next_ne_self S.three_le i).symm)).choose

theorem CenteredDiscPolygonSupportData.incident_mem_support {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    S.vertices i ∈ (S.supportLine i).closedCarrier ∧
      S.vertices (finRotate n i) ∈ (S.supportLine i).closedCarrier :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (S.vertices i) (S.vertices
    (finRotate n i))
    (S.vertices_injective.ne (centeredPolygonSupport_next_ne_self S.three_le i).symm)).choose_spec.1

theorem CenteredDiscPolygonSupportData.supportLine_equation {n : ℕ} (S : CenteredDiscPolygonSupportData n)
    (i : Fin n) (p : 𝕔𝔻) :
    p ∈ (S.supportLine i).closedCarrier ↔ inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)=S.offsets i := by
  let L := S.supportLine i
  have hn : S.normals i≠0 := by intro he;have hh:=S.normal_norm i;rw [he,norm_zero] at hh;norm_num at hh
  have hm : L.incenterNormal≠0 := by
    intro he
    have hh := L.toHalfPlane.incenterNormal_lorentz_unit
    change ‖L.incenterNormal‖^2-L.incenterOffset^2=1 at hh
    rw [he,norm_zero,zero_pow (by omega : 2≠0)] at hh
    nlinarith only [hh,sq_nonneg L.incenterOffset]
  have hpq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
    i)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (S.vertices_injective.ne
      (centeredPolygonSupport_next_ne_self S.three_le i).symm)
  have hpL := sub_eq_zero.mp ((L.closed_incenter_affine_zero_iff _).mpr (S.incident_mem_support i).1)
  have hqL := sub_eq_zero.mp ((L.closed_incenter_affine_zero_iff _).mpr (S.incident_mem_support i).2)
  obtain ⟨k,hk,hmk,htk⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_affine_normals_proportional (S.normals i) L.incenterNormal
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
      i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i)))
    (S.offsets i) L.incenterOffset hn hm hpq (S.incident i).1 (S.incident i).2 hpL hqL
  rw [← L.closed_incenter_affine_zero_iff]
  change inner ℝ L.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p)-L.incenterOffset=0 ↔ _
  rw [hmk,htk,real_inner_smul_left,← mul_sub,mul_eq_zero]
  simp only [hk,false_or,sub_eq_zero]

theorem centeredPolygonSupport_prev_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (finRotate n).symm i ≠ i := by
  intro he
  have hh := congrArg (finRotate n) he
  rw [Equiv.apply_symm_apply] at hh
  exact centeredPolygonSupport_next_ne_self hn i hh.symm

theorem centeredPolygonSupport_prev_ne_next {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    (finRotate n).symm i ≠ finRotate n i := by
  intro he
  have hh := congrArg (finRotate n) he
  rw [Equiv.apply_symm_apply] at hh
  exact centeredPolygonSupport_next_next_ne_self hn i hh.symm

def CenteredDiscPolygonSupportData.cornerTriangle {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := S.vertices i
  b := S.vertices ((finRotate n).symm i)
  c := S.vertices (finRotate n i)
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    have hac : S.vertices i ≠ S.vertices (finRotate n i) := by
      intro he
      exact centeredPolygonSupport_next_ne_self S.three_le i (S.vertices_injective he).symm
    have he : L = S.supportLine i := L.eq_of_two_closed_points (S.supportLine i) hac ha hc
      (S.incident_mem_support i).1 (S.incident_mem_support i).2
    rw [he] at hb
    have heq := (S.supportLine_equation i _).mp hb
    have hlt := S.nonincident i ((finRotate n).symm i)
      (centeredPolygonSupport_prev_ne_self S.three_le i) (centeredPolygonSupport_prev_ne_next S.three_le i)
    exact hlt.ne heq

theorem CenteredDiscPolygonSupportData.cornerTriangle_sideB {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    (S.cornerTriangle i).sideLineB = S.supportLine i := by
  let T := S.cornerTriangle i
  exact T.sideLineB.eq_of_two_closed_points (S.supportLine i) T.c_ne_a T.c_mem_sideLineB T.a_mem_sideLineB
    (S.incident_mem_support i).2 (S.incident_mem_support i).1

theorem CenteredDiscPolygonSupportData.cornerTriangle_sideC {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n) :
    (S.cornerTriangle i).sideLineC = S.supportLine ((finRotate n).symm i) := by
  let T := S.cornerTriangle i
  apply T.sideLineC.eq_of_two_closed_points _ T.a_ne_b T.a_mem_sideLineC T.b_mem_sideLineC
  · change S.vertices i ∈ (S.supportLine ((finRotate n).symm i)).closedCarrier
    simpa only [Equiv.apply_symm_apply] using (S.incident_mem_support ((finRotate n).symm i)).2
  · exact (S.incident_mem_support ((finRotate n).symm i)).1

theorem CenteredDiscPolygonSupportData.cornerTriangle_outgoing_cut {n : ℕ} (S : CenteredDiscPolygonSupportData n)
    (i : Fin n) (p : 𝕔𝔻) :
    inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) < S.offsets i ↔
      0 < ((S.cornerTriangle i).coordinate p).1 := by
  let T := S.cornerTriangle i
  let x := (T.coordinate p).1
  let s := inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
    ((finRotate n).symm i)))
  have hs : s < S.offsets i := S.nonincident i ((finRotate n).symm i)
    (centeredPolygonSupport_prev_ne_self S.three_le i) (centeredPolygonSupport_prev_ne_next S.three_le i)
  have he := T.inner_klein_reconstruction (S.normals i) p
  change inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) =
    inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) +
      x*(s-inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
        i))) +
      (T.coordinate p).2*(inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (S.vertices (finRotate n i)))-
        inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
          i))) at he
  rw [(S.incident i).1,(S.incident i).2,sub_self,mul_zero,add_zero] at he
  rw [he]
  constructor
  · intro h
    by_contra hx
    have hprod := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hx) (sub_nonpos.mpr hs.le)
    linarith only [h,hprod]
  · intro hx
    have hprod := mul_neg_of_pos_of_neg hx (sub_neg.mpr hs)
    linarith only [hprod]

theorem CenteredDiscPolygonSupportData.cornerTriangle_incoming_cut {n : ℕ} (S : CenteredDiscPolygonSupportData n)
    (i : Fin n) (p : 𝕔𝔻) :
    inner ℝ (S.normals ((finRotate n).symm i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p) < S.offsets ((finRotate n).symm i) ↔
      0 < ((S.cornerTriangle i).coordinate p).2 := by
  let T := S.cornerTriangle i
  let j := (finRotate n).symm i
  let y := (T.coordinate p).2
  let s := inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
    (finRotate n i)))
  have hji : finRotate n j = i := (finRotate n).apply_symm_apply i
  have hs : s < S.offsets j := by
    apply S.nonincident j (finRotate n i)
    · exact (centeredPolygonSupport_prev_ne_next S.three_le i).symm
    · rw [hji]
      exact centeredPolygonSupport_next_ne_self S.three_le i
  have ha : inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) = S.offsets j := by
    simpa only [hji] using (S.incident j).2
  have he := T.inner_klein_reconstruction (S.normals j) p
  change inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) =
    inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) +
      (T.coordinate p).1*(inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (S.vertices j))-
        inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
          i))) +
      y*(s-inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
        i))) at he
  rw [ha,(S.incident j).1,sub_self,mul_zero,add_zero] at he
  rw [he]
  constructor
  · intro h
    by_contra hy
    have hprod := mul_nonneg_of_nonpos_of_nonpos (not_lt.mp hy) (sub_nonpos.mpr hs.le)
    linarith only [h,hprod]
  · intro hy
    have hprod := mul_neg_of_pos_of_neg hy (sub_neg.mpr hs)
    linarith only [hprod]

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.centered_continuous_discCoordinate (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) : Continuous T.discCoordinate := by
  have he : T.discCoordinate = fun z : 𝔻 => T.ambientCoordinateHomeomorph (z : ℂ) :=
    funext (fun z => (T.ambientCoordinateHomeomorph_disc z).symm)
  rw [he]
  exact T.ambientCoordinateHomeomorph.continuous.comp Complex.UnitDisc.continuous_coe

theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.centered_mem_interior_iff_discCoordinate (T
  : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (z : 𝔻) :
    z ∈ T.interior ↔ 0 < (T.discCoordinate z).1 ∧ 0 < (T.discCoordinate z).2 ∧
      (T.discCoordinate z).1+(T.discCoordinate z).2 < 1 := by
  have he : T.complexInterior = T.ambientCoordinateHomeomorph ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle := by
    rw [← T.ambient_image_interior,Set.preimage_image_eq _ T.ambientCoordinateHomeomorph.injective]
  change (z : ℂ) ∈ T.complexInterior ↔ _
  rw [he]
  change T.ambientCoordinateHomeomorph (z :
    ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.standardOpenTriangle ↔ _
  rw [T.ambientCoordinateHomeomorph_disc]
  rfl

theorem CenteredDiscPolygonSupportData.cornerTriangle_interior_germ {n : ℕ} (S : CenteredDiscPolygonSupportData n)
    (i : Fin n) (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    ∀ᶠ w in 𝓝 z,w ∈ S.toDiscPolygon.interior ↔ w ∈ (S.cornerTriangle i).interior := by
  let T := S.cornerTriangle i
  have hcoord : T.discCoordinate z = (0,0) := by
    change T.coordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) = (0,0)
    rw [← hz]
    exact T.coordinate_a
  have hsum : ∀ᶠ w in 𝓝 z,(T.discCoordinate w).1+(T.discCoordinate w).2 < 1 := by
    apply (isOpen_lt (T.centered_continuous_discCoordinate.fst.add T.centered_continuous_discCoordinate.snd)
      continuous_const).mem_nhds
    change (T.discCoordinate z).1+(T.discCoordinate z).2 < 1
    rw [hcoord]
    norm_num
  have hother : ∀ j : Fin n,∀ᶠ w in 𝓝 z,j ≠ i → j ≠ (finRotate n).symm i →
      inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) < S.offsets j := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
    by_cases hjprev : j = (finRotate n).symm i
    · exact Filter.Eventually.of_forall (fun _ _ h => (h hjprev).elim)
    have hzj : inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) < S.offsets j := by
      rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion z,← hz]
      apply S.nonincident j i (Ne.symm hji)
      intro he
      apply hjprev
      exact (finRotate n).injective (by rw [Equiv.apply_symm_apply]; exact he.symm)
    have ho : IsOpen {w : 𝔻 | inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      w) < S.offsets j} :=
      isOpen_lt (continuous_const.inner
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate) continuous_const
    have hmem : ∀ᶠ w in 𝓝 z,inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      w) < S.offsets j := ho.mem_nhds hzj
    exact hmem.mono (fun _ h _ _ => h)
  filter_upwards [hsum,Filter.eventually_all.mpr hother] with w hsumw hotherw
  rw [S.toDiscPolygon_interior,T.centered_mem_interior_iff_discCoordinate]
  change (∀ j : Fin n,inner ℝ (S.normals j) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w) <
    S.offsets j) ↔ _
  constructor
  · intro hw
    exact ⟨(S.cornerTriangle_outgoing_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w)).mp
      (hw i),
      (S.cornerTriangle_incoming_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w)).mp (hw
        ((finRotate n).symm i)),hsumw⟩
  · rintro ⟨hx,hy,_⟩ j
    by_cases hji : j = i
    · subst j
      exact (S.cornerTriangle_outgoing_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        w)).mpr hx
    by_cases hjprev : j = (finRotate n).symm i
    · subst j
      exact (S.cornerTriangle_incoming_cut i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        w)).mpr hy
    exact hotherw j hji hjprev

theorem CenteredDiscPolygonSupportData.cornerRayPrev_eq {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n)
    (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    S.toDiscPolygon.cornerRayPrev i z hz = (S.cornerTriangle i).cornerRayABAtA z hz := by
  exact (S.cornerTriangle i).rayToward_b z hz _

theorem CenteredDiscPolygonSupportData.cornerRayNext_eq {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n)
    (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    S.toDiscPolygon.cornerRayNext i z hz = (S.cornerTriangle i).cornerRayACAtA z hz := by
  exact (S.cornerTriangle i).rayToward_c z hz _

theorem CenteredDiscPolygonSupportData.hasMinorInterior {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin n)
    (z : 𝔻) (hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    S.toDiscPolygon.HasMinorInteriorAt i z hz := by
  let T := S.cornerTriangle i
  change ∀ᶠ w in 𝓝 z,w ∈ S.toDiscPolygon.interior ↔ w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.properDiscAngleInterior
    (S.toDiscPolygon.cornerRayPrev i z hz) (S.toDiscPolygon.cornerRayNext i z hz)
  rw [S.cornerRayPrev_eq i z hz,S.cornerRayNext_eq i z hz]
  let centeredPolygonSupportAngleNativeMetric : MetricSpace 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨r,hr,he⟩ := T.cornerAtA_locally_interior z hz
  filter_upwards [S.cornerTriangle_interior_germ i z hz,Metric.ball_mem_nhds z hr] with w hw hball
  have hm := congrArg (fun U : Set 𝔻 => w ∈ U) he
  exact hw.trans (by simpa only [mem_inter_iff,hball,true_and] using iff_of_eq hm)

theorem CenteredDiscPolygonSupportData.angle_eq_cornerTriangle {n : ℕ} (S : CenteredDiscPolygonSupportData n) (i : Fin
  n) :
    S.toDiscPolygon.angle i = (S.cornerTriangle i).alpha := by
  let T := S.cornerTriangle i
  by_cases hi : ‖(S.vertices i : ℂ)‖ < 1
  · let z := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (S.vertices i) hi
    have hz : S.vertices i = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
    rw [S.toDiscPolygon.angle_of_minor i z hz (S.hasMinorInterior i z hz),
      S.cornerRayPrev_eq i z hz,S.cornerRayNext_eq i z hz,T.alpha_of_finite z hz]
  · have hi' := le_antisymm (S.vertices i).norm_le_one (le_of_not_gt hi)
    rw [S.toDiscPolygon.angle_of_ideal i hi',T.alpha_of_ideal hi']
end
end LowDimensionalTopology.Geometry.Polygon
