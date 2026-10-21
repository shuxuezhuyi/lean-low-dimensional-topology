/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonAngularOrder
public import Mathlib.Analysis.Convex.GaugeRescale
set_option backward.isDefEq.respectTransparency false
/-! # Genuine Jordan polygons from supporting half-planes

Cyclic native vertices and genuine supporting lines determine the entire boundary,
its bounded complementary region and its convexity. The hypotheses contain no
Jordan, triangulation, area or angle identity. The separate support-data construction
for prescribed ordered angles and the general nonconvex polygon theorems remain
unfinished.
-/

@[expose] public section
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Actual cyclic support data. No Jordan, triangulation, area or angle identity is assumed. -/
structure DiscPolygonSupportData (n : ℕ) where
  three_le : 3 ≤ n
  vertices : Fin n → 𝕔𝔻
  vertices_injective : Function.Injective vertices
  normals : Fin n → ℂ
  normal_norm : ∀ i,‖normals i‖ = 1
  offsets : Fin n → ℝ
  offset_mem : ∀ i,offsets i ∈ Ioo (0 : ℝ) 1
  incident : ∀ i,inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices
    i)) = offsets i ∧
    inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices (finRotate n
      i))) = offsets i
  nonincident : ∀ i j,j ≠ i → j ≠ finRotate n i →
    inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices
      j)) < offsets i
  region_subset_closedBall : {z : ℂ | ∀ i,inner ℝ (normals i) z ≤ offsets i} ⊆ Metric.closedBall 0 1

/-- The actual ambient intersection of all supporting closed half-planes. -/
def DiscPolygonSupportData.kleinRegion {n : ℕ} (S : DiscPolygonSupportData n) : Set ℂ :=
  {z | ∀ i,inner ℝ (S.normals i) z ≤ (S.offsets i)}

def DiscPolygonSupportData.strictKleinRegion {n : ℕ} (S : DiscPolygonSupportData n) : Set ℂ :=
  {z | ∀ i,inner ℝ (S.normals i) z < (S.offsets i)}

def DiscPolygonSupportData.supportLine {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin
  n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine (S.normals i) (S.offsets i) (S.normal_norm
    i) (S.offset_mem i)

theorem DiscPolygonSupportData.kleinRegion_isClosed {n : ℕ} (S : DiscPolygonSupportData n) : IsClosed S.kleinRegion := by
  have he : S.kleinRegion = ⋂ i,{z : ℂ | inner ℝ (S.normals i) z ≤ (S.offsets i)} := by ext z; simp [DiscPolygonSupportData.kleinRegion]
  rw [he]
  exact isClosed_iInter (fun i => isClosed_le (continuous_const.inner continuous_id) continuous_const)

theorem DiscPolygonSupportData.kleinRegion_convex {n : ℕ} (S : DiscPolygonSupportData n) : Convex ℝ S.kleinRegion := by
  have he : S.kleinRegion = ⋂ i,{z : ℂ | inner ℝ (S.normals i) z ≤ (S.offsets i)} := by ext z; simp [DiscPolygonSupportData.kleinRegion]
  rw [he]
  exact convex_iInter (fun i => convex_halfSpace_le (innerSL ℝ (S.normals i)).toLinearMap.isLinear (S.offsets i))

theorem DiscPolygonSupportData.kleinRegion_isCompact {n : ℕ} (S : DiscPolygonSupportData n) : IsCompact S.kleinRegion :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset S.kleinRegion_isClosed S.region_subset_closedBall

theorem DiscPolygonSupportData.strictKleinRegion_isOpen {n : ℕ} (S : DiscPolygonSupportData n) : IsOpen S.strictKleinRegion := by
  have he : S.strictKleinRegion = ⋂ i,{z : ℂ | inner ℝ (S.normals i) z < (S.offsets i)} := by ext z; simp [DiscPolygonSupportData.strictKleinRegion]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_const.inner continuous_id) continuous_const)

theorem DiscPolygonSupportData.strictKleinRegion_subset {n : ℕ} (S : DiscPolygonSupportData n) :
    S.strictKleinRegion ⊆ S.kleinRegion := fun _ hz i => (hz i).le

theorem DiscPolygonSupportData.origin_mem_strict {n : ℕ} (S : DiscPolygonSupportData n) :
    (0 : ℂ) ∈ S.strictKleinRegion := by
  intro i
  rw [inner_zero_right]
  exact (S.offset_mem i).1

/-- Each strictly feasible point really is an ambient interior point. -/
theorem DiscPolygonSupportData.strict_subset_interior {n : ℕ} (S : DiscPolygonSupportData n) :
    S.strictKleinRegion ⊆ interior S.kleinRegion :=
  interior_maximal S.strictKleinRegion_subset S.strictKleinRegion_isOpen

/-- Every actual ambient interior point satisfies all supporting inequalities strictly. -/
theorem DiscPolygonSupportData.interior_subset_strict {n : ℕ} (S : DiscPolygonSupportData n) :
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

theorem DiscPolygonSupportData.interior_kleinRegion {n : ℕ} (S : DiscPolygonSupportData n) :
    interior S.kleinRegion = S.strictKleinRegion :=
  subset_antisymm S.interior_subset_strict S.strict_subset_interior

theorem DiscPolygonSupportData.kleinRegion_interior_nonempty {n : ℕ} (S : DiscPolygonSupportData n) :
    (interior S.kleinRegion).Nonempty := ⟨0,S.strict_subset_interior S.origin_mem_strict⟩

theorem DiscPolygonSupportData.vertex_mem_region {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i) ∈ S.kleinRegion := by
  intro j
  by_cases hij : i = j
  · subst i
    exact (S.incident j).1.le
  · by_cases hij' : i = finRotate n j
    · subst i
      exact (S.incident j).2.le
    · exact (S.nonincident j i hij hij').le

theorem DiscPolygonSupportData.incident_mem_support {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    S.vertices i ∈ (S.supportLine i).closedCarrier ∧ S.vertices (finRotate n i) ∈ (S.supportLine i).closedCarrier := by
  constructor
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _
    _).mpr (S.incident i).1
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _
    _).mpr (S.incident i).2


/-- The support body is the closure of its genuine ambient interior. -/
theorem DiscPolygonSupportData.closure_strictKleinRegion {n : ℕ} (S : DiscPolygonSupportData n) :
    closure S.strictKleinRegion = S.kleinRegion := by
  rw [← S.interior_kleinRegion]
  exact (S.kleinRegion_convex.closure_interior_eq_closure_of_nonempty_interior
    S.kleinRegion_interior_nonempty).trans S.kleinRegion_isClosed.closure_eq

/-- A cyclic successor differs from the starting index when there are at least three vertices. -/
theorem polygonSupport_next_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
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

/-- A genuine polygon has no cyclic successor cycle of length two. -/
theorem polygonSupport_next_next_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
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

/-- The complete support-body boundary is a genuine topological circle. -/
theorem DiscPolygonSupportData.frontier_jordan {n : ℕ} (S : DiscPolygonSupportData n) :
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

/-- Outside the entire support body there is only one connected component. -/
theorem DiscPolygonSupportData.exterior_isPreconnected {n : ℕ} (S : DiscPolygonSupportData n) :
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

/-- The actual affine face of one support line. -/
def DiscPolygonSupportData.kleinFace {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) : Set ℂ :=
  {z | z ∈ S.kleinRegion ∧ inner ℝ (S.normals i) z = S.offsets i}

/-- Every boundary point lies on an actual active supporting line. -/
theorem DiscPolygonSupportData.frontier_eq_faces {n : ℕ} (S : DiscPolygonSupportData n) :
    frontier S.kleinRegion = ⋃ i,S.kleinFace i := by
  classical
  rw [frontier,S.kleinRegion_isClosed.closure_eq,S.interior_kleinRegion]
  ext z
  simp only [mem_sdiff,mem_iUnion,DiscPolygonSupportData.kleinFace,mem_ofPred_eq,DiscPolygonSupportData.strictKleinRegion]
  constructor
  · rintro ⟨hz,hnot⟩
    obtain ⟨i,hi⟩ := not_forall.mp hnot
    exact ⟨i,hz,le_antisymm (hz i) (not_lt.mp hi)⟩
  · rintro ⟨i,hz,hi⟩
    exact ⟨hz,fun hs => (ne_of_lt (hs i)) hi⟩

/-- The segment joining the two incident vertices lies in the complete active face. -/
theorem DiscPolygonSupportData.segment_subset_face {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) ⊆ S.kleinFace i := by
  rintro z ⟨a,b,ha,hb,hab,rfl⟩
  constructor
  · exact S.kleinRegion_convex (S.vertex_mem_region i) (S.vertex_mem_region (finRotate n i)) ha hb hab
  · rw [inner_add_right,real_inner_smul_right,real_inner_smul_right,(S.incident i).1,(S.incident i).2]
    rw [← add_mul,hab,one_mul]


/-- The origin and the endpoints of any genuine supporting edge are noncollinear. -/
def DiscPolygonSupportData.edgeTriangle {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle where
  a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : 𝔻)
  b := S.vertices i
  c := S.vertices (finRotate n i)
  noncollinear := by
    rintro ⟨L,h0,hp,hq⟩
    have hpq : S.vertices i ≠ S.vertices (finRotate n i) := by
      intro he
      exact polygonSupport_next_ne_self S.three_le i (S.vertices_injective he).symm
    have he : L = S.supportLine i := L.eq_of_two_closed_points (S.supportLine i) hpq hp hq
      (S.incident_mem_support i).1 (S.incident_mem_support i).2
    rw [he] at h0
    have heq := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _
      _).mp h0
    have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : 𝔻)) = 0 := by
      simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
    rw [hz,inner_zero_right] at heq
    exact (S.offset_mem i).1.ne' heq.symm

/-- No point of the actual support face lies beyond its two incident vertices. -/
theorem DiscPolygonSupportData.face_subset_segment {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    S.kleinFace i ⊆ segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) := by
  intro z hz
  let p : 𝕔𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph.symm
    (Complex.UnitClosedDisc.mk z (by simpa only [Metric.mem_closedBall,dist_zero_right] using S.region_subset_closedBall hz.1))
  have hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p = z := by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph.symm _)) : ℂ) = z
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinHomeomorph.apply_symm_apply]
    rfl
  let T := S.edgeTriangle i
  let x := (T.coordinate p).1
  let y := (T.coordinate p).2
  have hzero : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a = 0 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (0 : 𝔻)) = 0
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hsum : x+y = 1 := by
    have he := T.inner_klein_reconstruction (S.normals i) p
    change inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p) = inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) +
      x*(inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))
        - inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)) +
      y*(inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
        (finRotate n i))) - inner ℝ (S.normals i)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)) at he
    rw [hp,hzero,inner_zero_right,(S.incident i).1,(S.incident i).2,hz.2] at he
    have ht := (S.offset_mem i).1
    nlinarith only [he,ht]
  let prev := (finRotate n).symm i
  have hprev : finRotate n prev = i := (finRotate n).apply_symm_apply i
  have hpi : prev ≠ i := by
    intro he
    exact polygonSupport_next_ne_self S.three_le i (he ▸ hprev)
  have hpnext : finRotate n i ≠ prev := by
    intro he
    have hh := congrArg (finRotate n) he
    rw [hprev] at hh
    exact polygonSupport_next_next_ne_self S.three_le i hh
  have hyp : inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) = S.offsets prev := by
    simpa only [hprev] using (S.incident prev).2
  have hyq : inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    (S.vertices (finRotate n i))) < S.offsets prev :=
    S.nonincident prev (finRotate n i) hpnext (by rw [hprev]; exact polygonSupport_next_ne_self S.three_le i)
  have hy : 0 ≤ y := by
    have he := T.inner_klein_reconstruction (S.normals prev) p
    change inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p) = inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) +
      x*(inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
        i)) - inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)) +
      y*(inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
        (finRotate n i))) - inner ℝ (S.normals prev)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)) at he
    rw [hp,hzero,inner_zero_right,hyp] at he
    have hzprev := hz.1 prev
    by_contra hy
    have hneg : y < 0 := lt_of_not_ge hy
    have hm := mul_pos_of_neg_of_neg hneg (sub_neg.mpr hyq)
    have hs := congrArg (fun t : ℝ => t*S.offsets prev) hsum
    nlinarith only [he,hzprev,hm,hs]
  have hnext : finRotate n i ≠ i := polygonSupport_next_ne_self S.three_le i
  have hixi : i ≠ finRotate n i := hnext.symm
  have hixnext : i ≠ finRotate n (finRotate n i) := (polygonSupport_next_next_ne_self S.three_le i).symm
  have hxp : inner ℝ (S.normals (finRotate n
    i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)) < S.offsets (finRotate
    n i) :=
    S.nonincident (finRotate n i) i hixi hixnext
  have hxq := (S.incident (finRotate n i)).1
  have hx : 0 ≤ x := by
    have he := T.inner_klein_reconstruction (S.normals (finRotate n i)) p
    change inner ℝ (S.normals (finRotate n i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p) = inner ℝ (S.normals (finRotate n i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      T.a) +
      x*(inner ℝ (S.normals (finRotate n i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (S.vertices i)) - inner ℝ (S.normals (finRotate n i))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)) +
      y*(inner ℝ (S.normals (finRotate n i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
        (S.vertices (finRotate n i))) - inner ℝ (S.normals (finRotate n i))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a)) at he
    rw [hp,hzero,inner_zero_right,hxq] at he
    have hznext := hz.1 (finRotate n i)
    by_contra hx
    have hneg : x < 0 := lt_of_not_ge hx
    have hm := mul_pos_of_neg_of_neg hneg (sub_neg.mpr hxp)
    have hs := congrArg (fun t : ℝ => t*S.offsets (finRotate n i)) hsum
    nlinarith only [he,hznext,hm,hs]
  refine ⟨x,y,hx,hy,hsum,?_⟩
  have he := T.klein_reconstruction p
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p = _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a +
    x • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
      i)-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) +
    y • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n
      i))-_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate T.a) at he
  simpa only [hp,hzero,sub_zero,zero_add] using he.symm

theorem DiscPolygonSupportData.face_eq_segment {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    S.kleinFace i = segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))) :=
  subset_antisymm (S.face_subset_segment i) (S.segment_subset_face i)


/-- Distinct supporting edges meet only at the designated endpoints of either edge. -/
theorem DiscPolygonSupportData.face_inter_subset_endpoints {n : ℕ} (S : DiscPolygonSupportData n)
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
        exact polygonSupport_next_next_ne_self S.three_le j hh
      · intro hh
        exact polygonSupport_next_ne_self S.three_le i (hh.trans hinext.symm)
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

/-- Each actual native edge has precisely the full affine active face as its Klein image. -/
theorem DiscPolygonSupportData.edge_image_eq_face {n : ℕ} (S : DiscPolygonSupportData n) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' discPolygonEdge S.vertices i = S.kleinFace i := by
  rw [discPolygonEdge,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment,←
    S.face_eq_segment i]

/-- The actual cyclic geodesic trace is the entire boundary of the support body. -/
theorem DiscPolygonSupportData.boundary_image_eq_frontier {n : ℕ} (S : DiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' discPolygonBoundary S.vertices = frontier S.kleinRegion := by
  rw [discPolygonBoundary,Set.image_iUnion,S.frontier_eq_faces]
  exact iUnion_congr S.edge_image_eq_face

/-- The support inequalities prove genuine simple cyclic edge intersections. -/
theorem DiscPolygonSupportData.simple_edges {n : ℕ} (S : DiscPolygonSupportData n) :
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

/-- Support data construct an actual Jordan geodesic polygon; no Jordan assertion is assumed. -/
def DiscPolygonSupportData.toDiscPolygon {n : ℕ} (S : DiscPolygonSupportData n) : DiscPolygon n where
  three_le := S.three_le
  vertices := S.vertices
  vertices_injective := S.vertices_injective
  simple_edges := S.simple_edges
  jordanBoundary := by
    obtain ⟨h⟩ := S.frontier_jordan
    exact ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.homeomorphImage
      (discPolygonBoundary S.vertices)).trans ((Homeomorph.setCongr S.boundary_image_eq_frontier).trans h)⟩


/-- The ambient Klein homeomorphism takes the genuine native polygon boundary onto the body frontier. -/
theorem DiscPolygonSupportData.complexBoundary_image {n : ℕ} (S : DiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' S.toDiscPolygon.complexBoundary = frontier S.kleinRegion := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) ''
    discPolygonBoundary S.vertices) = _
  rw [Set.image_image]
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph_closed] using S.boundary_image_eq_frontier

/-- The ambient exterior in the source definition is exactly the exterior of the true support body. -/
theorem DiscPolygonSupportData.complexOutside_image {n : ℕ} (S : DiscPolygonSupportData n) :
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

/-- The true bounded Jordan component is precisely the strict support intersection. -/
theorem DiscPolygonSupportData.complexInterior_image {n : ℕ} (S : DiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' S.toDiscPolygon.complexInterior = S.strictKleinRegion := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' (S.toDiscPolygon.complexBoundaryᶜ \
    S.toDiscPolygon.complexOutside) = _
  rw [Set.image_sdiff _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.injective,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_compl,S.complexBoundary_image,
    S.complexOutside_image,frontier,S.kleinRegion_isClosed.closure_eq,S.interior_kleinRegion]
  ext z
  simp only [mem_sdiff,mem_compl_iff,not_and,not_not]
  constructor
  · rintro ⟨h,hz⟩
    exact h hz
  · intro hz
    exact ⟨fun _ => hz,S.strictKleinRegion_subset hz⟩

/-- Actual native interior membership is equivalent to the strict geometric support inequalities. -/
theorem DiscPolygonSupportData.toDiscPolygon_interior {n : ℕ} (S : DiscPolygonSupportData n) :
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

/-- Convexity follows from the true support inequalities, rather than being an additional field. -/
theorem DiscPolygonSupportData.toDiscPolygon_isConvex {n : ℕ} (S : DiscPolygonSupportData n) :
    S.toDiscPolygon.IsConvex := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S.toDiscPolygon.interior
  rw [S.toDiscPolygon_interior]
  have he : {z : 𝔻 | ∀ i,inner ℝ (S.normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) <
    S.offsets i} =
      ⋂ i,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt (S.normals i) (S.offsets i) := by ext z; simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt]
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.iInter (fun i =>
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discKleinCutLt_hConvex (S.normals i) (S.offsets i))

/-- The original geometric origin really lies in the constructed polygon interior. -/
theorem DiscPolygonSupportData.origin_mem_polygon {n : ℕ} (S : DiscPolygonSupportData n) :
    (0 : 𝔻) ∈ S.toDiscPolygon.interior := by
  rw [S.toDiscPolygon_interior]
  intro i
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻) = 0 := by
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  rw [hz,inner_zero_right]
  exact (S.offset_mem i).1



/-- The actual compactified polygon closure fills the entire support body. -/
theorem DiscPolygonSupportData.closedModelClosure_image {n : ℕ} (S : DiscPolygonSupportData n) :
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

/-- The ambient closure of the genuine bounded Jordan component has the prescribed body as image. -/
theorem DiscPolygonSupportData.complexClosure_image {n : ℕ} (S : DiscPolygonSupportData n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph '' closure S.toDiscPolygon.complexInterior = S.kleinRegion := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ambientKleinHomeomorph.image_closure,S.complexInterior_image,S.closure_strictKleinRegion]

end
end LowDimensionalTopology.Geometry.Polygon
