/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Polygon.Support.SupportedPolygonAngles
public import LowDimensionalTopology.Geometry.Polygon.Tangential.PolygonTangentialTriangle
/-! # Actual ordered tangential Jordan polygons

The original angle ranges and strict angle-sum bound construct genuine cyclic
native geodesic edges, their entire Jordan boundary and actual bounded convex
interior. All numeric angles are identified with the actual interior forward
angles, including ideal zero angles. The actual density path metric supplies
an inscribed disc with unique contact on every actual side. No Jordan, support,
angle identity or incircle condition is assumed in the existence theorem.
The converse bound for arbitrary polygons is a separate unfinished result.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Any interval with finitely many prescribed consecutive endpoints contains its points in one subinterval. -/
theorem polygonInterval_exists (m : ℕ) (f : ℕ → ℝ) {t : ℝ} (h0 : f 0 ≤ t)
    (hm : t ≤ f (m+1)) : ∃ i : Fin (m+1),f i ≤ t ∧ t ≤ f ((i : ℕ)+1) := by
  induction m with
  | zero => exact ⟨0,h0,hm⟩
  | succ m ih =>
    by_cases ht : t ≤ f (m+1)
    · obtain ⟨i,hi⟩ := ih ht
      exact ⟨i.castSucc,hi⟩
    · exact ⟨Fin.last (m+1),(not_le.mp ht).le,hm⟩

/-- Every actual complex direction admits a genuine circle parameter in one complete turn. -/
theorem polygon_complex_polar (z : ℂ) :
    ∃ t ∈ Icc (0 : ℝ) (2*Real.pi),z = ‖z‖ • polygonAngleUnit t := by
  have he : z = ‖z‖ • polygonAngleUnit z.arg := by
    simpa only [polygonAngleUnit,circleMap_zero,Complex.ofReal_one,one_mul,Complex.real_smul] using
      (Complex.norm_mul_exp_arg_mul_I z).symm
  by_cases harg : 0 ≤ z.arg
  · exact ⟨z.arg,⟨harg,by linarith only [Complex.arg_le_pi z,Real.pi_pos]⟩,he⟩
  · refine ⟨z.arg+2*Real.pi,⟨?_,?_⟩,?_⟩
    · linarith only [Complex.neg_pi_lt_arg z,Real.pi_pos]
    · linarith only [not_le.mp harg]
    · change z = ‖z‖ • circleMap 0 1 (z.arg+2*Real.pi)
      rw [periodic_circleMap 0 1]
      exact he

/-- A balanced positive-radius corner construction has at least one normal interval. -/
theorem polygonAngleBalance_ne_zero {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hb : polygonAngleBalance θ d = Real.pi) : n ≠ 0 := by
  intro hn
  subst n
  have hp := Real.pi_pos
  simp only [polygonAngleBalance,Finset.univ_eq_empty,Finset.sum_empty] at hb
  linarith only [hp,hb]


/-- The full-turn angle balance automatically forces at least three actual vertices. -/
theorem polygonAngleBalance_three_le {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) : 3 ≤ n := by
  have hn := polygonAngleBalance_ne_zero θ d hb
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hi : (⟨0,by omega⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
  have hsum : ∑ i : Fin n,polygonTangentialHalfAngle (θ i) d < ∑ _i : Fin n,Real.pi/2 :=
    Finset.sum_lt_sum (fun i _ => (polygonTangentialHalfAngle_bounds (hθ i) hd).2.le)
      ⟨⟨0,by omega⟩,hi,(polygonTangentialHalfAngle_bounds (hθ ⟨0,by omega⟩) hd).2⟩
  have hb' : ∑ i : Fin n,polygonTangentialHalfAngle (θ i) d = Real.pi := hb
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hb'] at hsum
  by_contra hlt
  have hn2 : n ≤ 2 := by omega
  have hn2' : (n : ℝ) ≤ 2 := by exact_mod_cast hn2
  have hp := mul_nonneg (sub_nonneg.mpr hn2') (Real.pi_pos.le)
  nlinarith only [hsum,hp]

/-- Support bounds at the last normal are exactly the bound at the first normal. -/
theorem polygonNormalSupport_bound_nat {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hb : polygonAngleBalance θ d = Real.pi) (z : ℂ)
    (hz : ∀ i : Fin n,inner ℝ (polygonAngleUnit (polygonNormalAngle θ d i)) z ≤ Real.tanh d)
    {k : ℕ} (hk : k ≤ n) :
    inner ℝ (polygonAngleUnit (polygonNormalAngle θ d k)) z ≤ Real.tanh d := by
  by_cases hkn : k < n
  · exact hz ⟨k,hkn⟩
  · have he : k = n := by omega
    rw [he,polygonNormalAngle_total θ d hb,polygonAngleUnit_two_pi]
    have hn := polygonAngleBalance_ne_zero θ d hb
    simpa only [Fin.val_zero,polygonNormalAngle_zero] using hz ⟨0,by omega⟩

/-- Every actual direction has a supporting unit normal whose directional cosine is at least the radius. -/
theorem polygonNormalAngle_direction_cover {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (2*Real.pi)) :
    ∃ k ≤ n,Real.tanh d ≤ Real.cos (t-polygonNormalAngle θ d k) := by
  have hn := polygonAngleBalance_ne_zero θ d hb
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h0 : polygonNormalAngle θ d 0 ≤ t := by rw [polygonNormalAngle_zero]; exact ht.1
  have hn' : t ≤ polygonNormalAngle θ d (m+1) := by rw [show m+1 = n from hm.symm,polygonNormalAngle_total θ d hb]; exact ht.2
  obtain ⟨i',hi⟩ := polygonInterval_exists m (polygonNormalAngle θ d) h0 hn'
  let i : Fin n := ⟨i'.val,by rw [hm]; exact i'.isLt⟩
  have histep := polygonNormalAngle_succ θ d i
  have hα := polygonTangentialHalfAngle_bounds (hθ i) hd
  have hαpi : polygonTangentialHalfAngle (θ i) d ≤ Real.pi := by linarith only [hα.2,Real.pi_pos]
  have hcpos := polygonTangentialHalfAngle_cos_pos (hθ i) hd
  have hrcos : Real.tanh d ≤ Real.cos (polygonTangentialHalfAngle (θ i) d) := by
    exact (div_le_one hcpos).mp (polygonTangentialVertexCoordinate_le_one (hθ i) hd)
  change polygonNormalAngle θ d i ≤ t ∧ t ≤ polygonNormalAngle θ d ((i : ℕ)+1) at hi
  by_cases hmid : t ≤ polygonNormalAngle θ d i + polygonTangentialHalfAngle (θ i) d
  · refine ⟨i,i.isLt.le,hrcos.trans ?_⟩
    exact Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr hi.1) hαpi (by linarith only [hmid])
  · refine ⟨(i : ℕ)+1,i.isLt,hrcos.trans ?_⟩
    rw [show t-polygonNormalAngle θ d ((i : ℕ)+1) = -(polygonNormalAngle θ d ((i : ℕ)+1)-t) by ring,Real.cos_neg]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr hi.2) hαpi
      (by linarith only [not_le.mp hmid,histep])

/-- The intersection of all actual ordered tangent half-planes stays inside the true closed Klein disc. -/
theorem polygonOrderedSupport_region_subset_closedBall {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) :
    {z : ℂ | ∀ i : Fin n,inner ℝ (polygonAngleUnit (polygonNormalAngle θ d i)) z ≤ Real.tanh d} ⊆
      Metric.closedBall 0 1 := by
  intro z hz
  obtain ⟨t,ht,he⟩ := polygon_complex_polar z
  obtain ⟨k,hk,hcos⟩ := polygonNormalAngle_direction_cover θ d hθ hd hb ht
  have hw := polygonNormalSupport_bound_nat θ d hb z hz hk
  rw [he,real_inner_smul_right,polygonAngleUnit_inner] at hw
  have hcospos : 0 < Real.cos (t-polygonNormalAngle θ d k) :=
    lt_of_lt_of_le (polygonTangential_tanh_pos hd) hcos
  have hnorm : ‖z‖ ≤ 1 := (le_div_iff₀ hcospos).mpr hw |>.trans ((div_le_one hcospos).mpr hcos)
  simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm


/-- Cyclically identified normal directions agree with the actual full-turn construction. -/
theorem polygonNormalAngle_unit_next {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hb : polygonAngleBalance θ d = Real.pi) (i : Fin n) :
    polygonAngleUnit (polygonNormalAngle θ d (finRotate n i)) =
      polygonAngleUnit (polygonNormalAngle θ d ((i : ℕ)+1)) := by
  by_cases hi : (i : ℕ)+1 < n
  · rw [polygon_finRotate_val_of_succ_lt i hi]
  · have hn : (i : ℕ)+1 = n := by omega
    rw [polygon_finRotate_val_of_last i hn,hn,polygonNormalAngle_zero,
      polygonNormalAngle_total θ d hb,polygonAngleUnit_two_pi]

/-- The original balance produces actual cyclic support data with every geometric condition proved. -/
def polygonOrderedSupportData {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) : DiscPolygonSupportData n where
  three_le := polygonAngleBalance_three_le θ d hθ hd hb
  vertices := polygonOrderedTangentialVertex θ d hθ hd
  vertices_injective := polygonOrderedTangentialVertex_injective θ d hθ hd hb
  normals := fun i => polygonAngleUnit (polygonNormalAngle θ d (finRotate n i))
  normal_norm := fun i => polygonAngleUnit_norm _
  offsets := fun _ => Real.tanh d
  offset_mem := fun _ => ⟨polygonTangential_tanh_pos hd,Real.tanh_lt_one d⟩
  incident := by
    intro i
    constructor
    · rw [polygonNormalAngle_unit_next θ d hb i]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _ _).mp
        (polygonOrderedTangentialVertex_outgoing θ d hθ hd i)
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_closed_equation_iff _ _ _ _ _).mp
        (polygonOrderedTangentialVertex_incoming θ d hθ hd (finRotate n i))
  nonincident := by
    intro i j hji hjnext
    apply polygonOrderedTangentialVertex_support_strict θ d hθ hd hb j (finRotate n i) hjnext.symm
    intro he
    exact hji ((finRotate n).injective he).symm
  region_subset_closedBall := by
    intro z hz
    apply polygonOrderedSupport_region_subset_closedBall θ d hθ hd hb
    intro i
    have h := hz ((finRotate n).symm i)
    change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n ((finRotate n).symm i))))
      z ≤ Real.tanh d at h
    simpa only [Equiv.apply_symm_apply] using h

/-- A genuine ordered convex Jordan polygon built from the original angle-balance data. -/
def polygonTangentialPolygon {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) : DiscPolygon n :=
  (polygonOrderedSupportData θ d hθ hd hb).toDiscPolygon

theorem polygonTangentialPolygon_vertices {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) :
    (polygonTangentialPolygon θ d hθ hd hb).vertices = polygonOrderedTangentialVertex θ d hθ hd := rfl

theorem polygonTangentialPolygon_isConvex {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) :
    (polygonTangentialPolygon θ d hθ hd hb).IsConvex :=
  (polygonOrderedSupportData θ d hθ hd hb).toDiscPolygon_isConvex

theorem polygonTangentialPolygon_origin_mem {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) :
    (0 : 𝔻) ∈ (polygonTangentialPolygon θ d hθ hd hb).interior :=
  (polygonOrderedSupportData θ d hθ hd hb).origin_mem_polygon

/-- The prescribed angle-sum hypothesis yields an actual convex Jordan polygon, rather than just candidate vertices. -/
theorem exists_orderedTangentialPolygon {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hsum : ∑ i,θ i < ((n : ℝ)-2)*Real.pi) :
    ∃ (d : ℝ) (hd : 0 < d) (_hb : polygonAngleBalance θ d = Real.pi),∃ P : DiscPolygon n,
      P.IsConvex ∧ (0 : 𝔻) ∈ P.interior ∧
      P.vertices = polygonOrderedTangentialVertex θ d hθ hd := by
  obtain ⟨d,hd,hb⟩ := polygonAngleBalance_exists_positive θ hθ hsum
  exact ⟨d,hd,hb,polygonTangentialPolygon θ d hθ hd hb,
    polygonTangentialPolygon_isConvex θ d hθ hd hb,polygonTangentialPolygon_origin_mem θ d hθ hd hb,rfl⟩


/-- The true native polygon interior is the intersection of the constructed strict support half-planes. -/
theorem polygonTangentialPolygon_interior {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) :
    (polygonTangentialPolygon θ d hθ hd hb).interior =
      {z : 𝔻 | ∀ i : Fin n,inner ℝ (polygonAngleUnit (polygonNormalAngle θ d i)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) < Real.tanh d} := by
  change (polygonOrderedSupportData θ d hθ hd hb).toDiscPolygon.interior = _
  rw [DiscPolygonSupportData.toDiscPolygon_interior]
  ext z
  constructor
  · intro hz i
    have h := hz ((finRotate n).symm i)
    change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n ((finRotate n).symm i))))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) < Real.tanh d at h
    simpa only [Equiv.apply_symm_apply] using h
  · intro hz i
    exact hz (finRotate n i)

/-- Each actual supporting side has its own genuine finite radius foot. -/
def polygonOrderedTangentialFoot {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (hd : 0 < d) (k : ℕ) : 𝔻 :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.symm (Complex.UnitDisc.mk (Real.tanh d • polygonAngleUnit (polygonNormalAngle θ d k)) (by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (polygonTangential_tanh_pos hd),polygonAngleUnit_norm,mul_one]
    exact Real.tanh_lt_one d))

theorem polygonOrderedTangentialFoot_coordinate {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (hd : 0 < d) (k : ℕ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (polygonOrderedTangentialFoot θ d hd k) =
      Real.tanh d • polygonAngleUnit (polygonNormalAngle θ d k) :=
  congrArg (fun z : 𝔻 => (z : ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinHomeomorph.apply_symm_apply _)

/-- The contact foot has exactly the requested genuine hyperbolic path radius. -/
theorem polygonOrderedTangentialFoot_distance {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (hd : 0 < d) (k : ℕ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 (polygonOrderedTangentialFoot θ d hd k) = d := by
  apply Real.tanh_injective
  rw [← kleinCoordinate_norm_eq_tanh_distance,polygonOrderedTangentialFoot_coordinate,norm_smul,
    Real.norm_eq_abs,abs_of_pos (polygonTangential_tanh_pos hd),polygonAngleUnit_norm,mul_one]

/-- Each finite contact foot lies on the actual closed cyclic edge, not merely on its whole support line. -/
theorem polygonTangentialPolygon_foot_mem_edge {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (polygonOrderedTangentialFoot θ d hd (finRotate
      n i)) ∈
      discPolygonEdge (polygonTangentialPolygon θ d hθ hd hb).vertices i := by
  let S := polygonOrderedSupportData θ d hθ hd hb
  let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (polygonOrderedTangentialFoot θ d hd
    (finRotate n i))
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p ∈ S.kleinFace i := by
    constructor
    · intro j
      change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n j)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) ≤ Real.tanh d
      change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n j)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (polygonOrderedTangentialFoot θ d hd
          (finRotate n i))) ≤ Real.tanh d
      rw [polygonOrderedTangentialFoot_coordinate,real_inner_smul_right]
      calc
        _ ≤ Real.tanh d * (‖polygonAngleUnit (polygonNormalAngle θ d (finRotate n j))‖ *
            ‖polygonAngleUnit (polygonNormalAngle θ d (finRotate n i))‖) :=
          mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (polygonTangential_tanh_pos hd).le
        _ = Real.tanh d := by simp only [polygonAngleUnit_norm,mul_one]
    · change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n i)))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (polygonOrderedTangentialFoot θ d hd
          (finRotate n i))) = Real.tanh d
      rw [polygonOrderedTangentialFoot_coordinate,real_inner_smul_right,real_inner_self_eq_norm_sq,
        polygonAngleUnit_norm,one_pow,mul_one]
  rw [← S.edge_image_eq_face i] at hK
  obtain ⟨q,hq,he⟩ := hK
  have he' : q = p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he
  change p ∈ discPolygonEdge S.vertices i
  rw [← he']
  exact hq

/-- The actual hyperbolic open radius-d ball is contained in the genuine polygon interior. -/
theorem polygonTangentialPolygon_ball_subset {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) (z : 𝔻) (hz :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z < d) :
    z ∈ (polygonTangentialPolygon θ d hθ hd hb).interior := by
  rw [polygonTangentialPolygon_interior]
  intro i
  have htan : Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) < Real.tanh d :=
    (Real.artanh_lt_artanh_iff ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
      ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩).mp (by simpa only [Real.artanh_tanh] using hz)
  calc
    _ ≤ ‖polygonAngleUnit (polygonNormalAngle θ d
      i)‖ * ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ := real_inner_le_norm _ _
    _ = Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) := by rw [polygonAngleUnit_norm,one_mul,kleinCoordinate_norm_eq_tanh_distance]
    _ < Real.tanh d := htan


/-- The actual outward tangent supports have Lorentz-unit normal vectors. -/
theorem polygonOrderedNormal_lorentz_unit {n : ℕ} (θ : Fin n → ℝ) (d : ℝ) (k : ℕ) :
    ‖-(Real.cosh d • polygonAngleUnit (polygonNormalAngle θ d k))‖^2 - (-Real.sinh d)^2 = 1 := by
  rw [norm_neg,norm_smul,Real.norm_eq_abs,polygonAngleUnit_norm,mul_one,sq_abs,neg_sq]
  exact Real.cosh_sq_sub_sinh_sq d

/-- The actual adjacent outward normals recover the prescribed angle through their genuine Lorentz pairing. -/
theorem polygonOrderedNormal_lorentz_pair {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hb : polygonAngleBalance θ d = Real.pi) (i : Fin n) :
    inner ℝ (Real.cosh d • polygonAngleUnit (polygonNormalAngle θ d (finRotate n i)))
      (Real.cosh d • polygonAngleUnit (polygonNormalAngle θ d i)) - Real.sinh d^2 = -Real.cos (θ i) := by
  have he : inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n i)))
      (polygonAngleUnit (polygonNormalAngle θ d i)) =
      inner ℝ (polygonTangentialNormal (θ i) d 1) (polygonTangentialNormal (θ i) d (-1)) := by
    rw [polygonNormalAngle_unit_next θ d hb i,polygonAngleUnit_inner,polygonNormalAngle_succ]
    rw [show polygonNormalAngle θ d i -
      (polygonNormalAngle θ d i+2*polygonTangentialHalfAngle (θ i) d) =
      -(2*polygonTangentialHalfAngle (θ i) d) by ring,Real.cos_neg]
    rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
    simp only [polygonTangentialNormal,one_mul,neg_one_mul]
    rw [Real.cos_two_mul]
    nlinarith only [Real.sin_sq_add_cos_sq (polygonTangentialHalfAngle (θ i) d)]
  rw [real_inner_smul_left,real_inner_smul_right,he]
  simpa only [real_inner_smul_left,real_inner_smul_right] using
    (polygonTangentialSide_normal_pair (d := d) (hθ i))

/-- Every actual interior angle of the constructed Jordan polygon equals its prescribed value, including zero at ideal vertices. -/
theorem polygonTangentialPolygon_angle {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) (i : Fin n) :
    (polygonTangentialPolygon θ d hθ hd hb).angle i = θ i := by
  let S := polygonOrderedSupportData θ d hθ hd hb
  let T := S.cornerTriangle i
  change S.toDiscPolygon.angle i = θ i
  rw [S.angle_eq_cornerTriangle i]
  let n := -(Real.cosh d • polygonAngleUnit (polygonNormalAngle θ d (finRotate n i)))
  let m := -(Real.cosh d • polygonAngleUnit (polygonNormalAngle θ d i))
  have hn : ‖n‖^2 - (-Real.sinh d)^2 = 1 := polygonOrderedNormal_lorentz_unit θ d (finRotate _ i)
  have hm : ‖m‖^2 - (-Real.sinh d)^2 = 1 := polygonOrderedNormal_lorentz_unit θ d i
  have hB (z : 𝔻) (hz : z ∈ T.sideLineB.carrier) : inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = -Real.sinh d := by
    change z ∈ (S.cornerTriangle i).sideLineB.carrier at hz
    rw [S.cornerTriangle_sideB i] at hz
    have he := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ z).mp hz
    change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate _
      i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = Real.tanh d at he
    change inner ℝ (-(Real.cosh d • polygonAngleUnit (polygonNormalAngle θ d (finRotate _
      i)))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = _
    rw [inner_neg_left,real_inner_smul_left,he,Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos d).ne']
  have hC (z : 𝔻) (hz : z ∈ T.sideLineC.carrier) : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = -Real.sinh d := by
    change z ∈ (S.cornerTriangle i).sideLineC.carrier at hz
    rw [S.cornerTriangle_sideC i] at hz
    have he := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinTangentDiscLine_equation_iff _ _ _ _ z).mp hz
    change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate _ ((finRotate _).symm i))))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = Real.tanh d at he
    rw [Equiv.apply_symm_apply] at he
    change inner ℝ (-(Real.cosh d • polygonAngleUnit (polygonNormalAngle θ d
      i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = _
    rw [inner_neg_left,real_inner_smul_left,he,Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos d).ne']
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻) = 0 := by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.poincareToKlein,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula]
  have hqn : 0 < inner ℝ n (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻)) - (-Real.sinh d) := by
    rw [hz,inner_zero_right,sub_neg_eq_add,zero_add]
    exact Real.sinh_pos_iff.mpr hd
  have hqm : 0 < inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (0 : 𝔻)) - (-Real.sinh d) := by
    rw [hz,inner_zero_right,sub_neg_eq_add,zero_add]
    exact Real.sinh_pos_iff.mpr hd
  have he := T.cosine_alpha_inward_normalized_equations (0 : 𝔻) n m (-Real.sinh d) (-Real.sinh d)
    (S.cornerTriangle_origin_coordinates i) hn hm hB hC hqn hqm
  have hp : inner ℝ n m - (-Real.sinh d)*(-Real.sinh d) = -Real.cos (θ i) := by
    dsimp only [n,m]
    rw [inner_neg_left,inner_neg_right,neg_neg,neg_mul_neg]
    simpa only [pow_two] using polygonOrderedNormal_lorentz_pair θ d hθ hb i
  have hc : Real.cos T.alpha = Real.cos (θ i) := by linarith only [he,hp]
  exact Real.strictAntiOn_cos.injOn ⟨T.alpha_mem_Ico.1,T.alpha_mem_Ico.2.le⟩ ⟨(hθ i).1,(hθ i).2.le⟩ hc


/-- Every actual finite point of an edge is at least the incircle radius from the actual center. -/
theorem polygonTangentialPolygon_edge_distance_lower {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) (i : Fin n) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ discPolygonEdge
      (polygonTangentialPolygon θ d hθ hd hb).vertices i) :
    d ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z := by
  let S := polygonOrderedSupportData θ d hθ hd hb
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) ∈ S.kleinFace i :=
    S.edge_image_eq_face i ▸ mem_image_of_mem _ hz
  have he : inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n
    i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = Real.tanh d := hK.2
  have hle : Real.tanh d ≤ Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) := by
    calc
      Real.tanh d = inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n
        i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) := he.symm
      _ ≤ ‖polygonAngleUnit (polygonNormalAngle θ d (finRotate n
        i))‖ * ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ := real_inner_le_norm _ _
      _ = Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) := by rw [polygonAngleUnit_norm,one_mul,kleinCoordinate_norm_eq_tanh_distance]
  have h := (Real.artanh_le_artanh_iff ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
    ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩).mpr hle
  simpa only [Real.artanh_tanh] using h

/-- Each actual edge meets the actual radius-d circle in exactly its constructed finite tangency foot. -/
theorem polygonTangentialPolygon_foot_unique {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) (i : Fin n) (z : 𝔻)
    (hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ discPolygonEdge
      (polygonTangentialPolygon θ d hθ hd hb).vertices i)
    (hdz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z = d) : z = polygonOrderedTangentialFoot θ d hd (finRotate n i) := by
  let S := polygonOrderedSupportData θ d hθ hd hb
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) ∈ S.kleinFace i :=
    S.edge_image_eq_face i ▸ mem_image_of_mem _ hz
  have he : inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n
    i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) = Real.tanh d := hK.2
  have hn : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ = Real.tanh d := by rw [kleinCoordinate_norm_eq_tanh_distance,hdz]
  have hdiff : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z - Real.tanh d • polygonAngleUnit (polygonNormalAngle θ d (finRotate n i))‖^2 = 0 := by
    rw [norm_sub_sq_real,hn,norm_smul,Real.norm_eq_abs,abs_of_pos (polygonTangential_tanh_pos hd),
      polygonAngleUnit_norm,mul_one,real_inner_smul_right,real_inner_comm,he]
    ring
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective
  rw [polygonOrderedTangentialFoot_coordinate]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hdiff))

/-- The true closed hyperbolic incircle disc lies in the actual compactified polygon closure. -/
theorem polygonTangentialPolygon_closedBall_subset_closure {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) (z : 𝔻) (hz :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z ≤ d) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (polygonTangentialPolygon θ d hθ hd hb).interior := by
  let S := polygonOrderedSupportData θ d hθ hd hb
  have htan : Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) ≤ Real.tanh d :=
    (Real.artanh_le_artanh_iff ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩
      ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩).mp (by simpa only [Real.artanh_tanh] using hz)
  have hK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) ∈ S.kleinRegion := by
    intro i
    change inner ℝ (polygonAngleUnit (polygonNormalAngle θ d (finRotate n
      i))) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z) ≤ Real.tanh d
    calc
      _ ≤ ‖polygonAngleUnit (polygonNormalAngle θ d (finRotate n
        i))‖ * ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z‖ := real_inner_le_norm _ _
      _ = Real.tanh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 z) := by rw [polygonAngleUnit_norm,one_mul,kleinCoordinate_norm_eq_tanh_distance]
      _ ≤ Real.tanh d := htan
  rw [← S.closedModelClosure_image] at hK
  obtain ⟨p,hp,he⟩ := hK
  have he' := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S.toDiscPolygon.interior
  rw [← he']
  exact hp

/-- A genuine hyperbolic incircle is an actual interior metric disc with unique contact on every actual side. -/
def DiscPolygon.HasIncircleAt {n : ℕ} (P : DiscPolygon n) (q : 𝔻) (r : ℝ) : Prop :=
  0 < r ∧ (∀ z : 𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist q z < r → z ∈ P.interior) ∧
    (∀ z : 𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist q z ≤ r →
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure P.interior) ∧
    ∀ i : Fin n,∃ p : 𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel p ∈ discPolygonEdge P.vertices i ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist q p = r ∧
      ∀ z : 𝔻,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z ∈ discPolygonEdge P.vertices i → _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist q z = r → z = p

/-- All actual cyclic sides of the constructed polygon touch its true inscribed metric disc. -/
theorem polygonTangentialPolygon_hasIncircle {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : polygonAngleBalance θ d = Real.pi) :
    (polygonTangentialPolygon θ d hθ hd hb).HasIncircleAt 0 d := by
  refine ⟨hd,polygonTangentialPolygon_ball_subset θ d hθ hd hb,
    polygonTangentialPolygon_closedBall_subset_closure θ d hθ hd hb,?_⟩
  intro i
  exact ⟨polygonOrderedTangentialFoot θ d hd (finRotate n i),polygonTangentialPolygon_foot_mem_edge θ d hθ hd hb i,
    polygonOrderedTangentialFoot_distance θ d hd _,polygonTangentialPolygon_foot_unique θ d hθ hd hb i⟩

/-- The original prescribed ordered angles are realized by an actual convex Jordan polygon with a genuine incircle. -/
theorem exists_tangentialDiscPolygon {n : ℕ} (θ : Fin n → ℝ)
    (hθ : ∀ i,θ i ∈ Ico (0 : ℝ) Real.pi) (hsum : ∑ i,θ i < ((n : ℝ)-2)*Real.pi) :
    ∃ P : DiscPolygon n,P.IsConvex ∧ (∀ i,P.angle i = θ i) ∧ ∃ d,P.HasIncircleAt 0 d := by
  obtain ⟨d,hd,hb⟩ := polygonAngleBalance_exists_positive θ hθ hsum
  exact ⟨polygonTangentialPolygon θ d hθ hd hb,polygonTangentialPolygon_isConvex θ d hθ hd hb,
    polygonTangentialPolygon_angle θ d hθ hd hb,d,polygonTangentialPolygon_hasIncircle θ d hθ hd hb⟩

end
end LowDimensionalTopology.Geometry.Polygon
