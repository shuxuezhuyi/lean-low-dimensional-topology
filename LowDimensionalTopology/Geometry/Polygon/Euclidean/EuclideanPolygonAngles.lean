/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.PlaneSeparation
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonArea
public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Analysis.Convex.Join
/-! # Actual Euclidean Jordan polygon angles

The original Euclidean polygon is a genuine planar Jordan curve. Its interior
angles are defined from the angular measure of the original local region germ,
independently of a triangle mesh. The actual filled triangle corner measure is
identified with Mathlib's ordinary Euclidean angle, and genuine finite fans add.

The original canonical mesh and its actual Euler characteristic then prove the
full interior-angle sum for every simple polygon, including reflex and straight
corners. No convexity, angle budget or triangulation input is required.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory InnerProductGeometry
open scoped Classical Complex.UnitDisc ENNReal NNReal
namespace LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh
noncomputable section

/-- The genuine Euclidean angle at an ordered corner of an actual mesh face. -/
def euclideanCornerAngle (M : TriangleMesh) (t : M.Triangle) (i : Fin 3) : ℝ :=
  ![EuclideanGeometry.angle (M.position (M.orderedVertex t 1))
      (M.position (M.orderedVertex t 0)) (M.position (M.orderedVertex t 2)),
    EuclideanGeometry.angle (M.position (M.orderedVertex t 2))
      (M.position (M.orderedVertex t 1)) (M.position (M.orderedVertex t 0)),
    EuclideanGeometry.angle (M.position (M.orderedVertex t 0))
      (M.position (M.orderedVertex t 2)) (M.position (M.orderedVertex t 1))] i

theorem euclideanCornerAngle_sum (M : TriangleMesh) (t : M.Triangle) :
    ∑ i : Fin 3,M.euclideanCornerAngle t i = Real.pi := by
  have hne : M.position (M.orderedVertex t 1) ≠ M.position (M.orderedVertex t 0) :=
    M.position_injective.ne ((M.orderedVertex_injective t).ne (by decide : (1 : Fin 3) ≠ 0))
  have hh := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (M.position (M.orderedVertex t 2)) hne
  simpa [euclideanCornerAngle,Fin.sum_univ_succ,EuclideanGeometry.angle_comm,
    add_assoc,add_left_comm,add_comm] using hh

/-- The sum of actual incident Euclidean triangle angles at a used geometric vertex. -/
def euclideanAngleSumAt (M : TriangleMesh) (v : {v : M.Vertex // v ∈ M.usedVertices}) : ℝ :=
  ∑ t : M.Triangle,∑ i : Fin 3,
    if M.orderedVertex t i = v.1 then M.euclideanCornerAngle t i else 0

theorem sum_euclideanAngleSumAt (M : TriangleMesh) :
    (∑ v : {v : M.Vertex // v ∈ M.usedVertices},M.euclideanAngleSumAt v) =
      M.triangles.card*Real.pi := by
  unfold euclideanAngleSumAt
  rw [Finset.sum_comm]
  have hPoint (t : M.Triangle) :
      (∑ v : {v : M.Vertex // v ∈ M.usedVertices},∑ i : Fin 3,
        if M.orderedVertex t i=v.1 then M.euclideanCornerAngle t i else 0) = Real.pi := by
    rw [Finset.sum_comm]
    rw [← M.euclideanCornerAngle_sum t]
    apply Finset.sum_congr rfl
    intro i hi
    let v : {v : M.Vertex // v ∈ M.usedVertices} := ⟨M.orderedVertex t i,
      M.mem_usedVertices.mpr ⟨t.1,t.2,M.orderedVertex_mem t i⟩⟩
    rw [Finset.sum_eq_single v]
    · exact ite_eq_left rfl
    · intro w hwm hwv
      apply ite_eq_right
      intro he
      exact hwv (Subtype.ext he.symm)
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  simp_rw [hPoint]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe]

end
end LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh

namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- Actual positive rays meeting a set, without a chosen metric or polygon mesh. -/
def euclideanRayDirections (S : Set ℂ) (x : ℂ) : Set Circle :=
  {u | ∃ r : ℝ,0 < r ∧ x+r • (u : ℂ) ∈ S}

/-- Directions belonging to the actual local closed-region germ at the basepoint. -/
def euclideanLocalDirections (S : Set ℂ) (x : ℂ) : Set Circle :=
  {u | ∀ᶠ r in 𝓝[>] (0 : ℝ),x+r • (u : ℂ) ∈ S}

theorem euclideanRayDirections_eq_local {S : Set ℂ} {x : ℂ}
    (hS : Convex ℝ S) (hx : x ∈ S) :
    euclideanRayDirections S x = euclideanLocalDirections S x := by
  ext u
  change (∃ r : ℝ,0 < r ∧ x+r • (u : ℂ) ∈ S) ↔
    ∀ᶠ r in 𝓝[>] (0 : ℝ),x+r • (u : ℂ) ∈ S
  constructor
  · rintro ⟨r,hr,hw⟩
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    have hh := hS.add_smul_mem hx hw
      (show t/r ∈ Icc (0 : ℝ) 1 from ⟨div_nonneg ht.1.le hr.le,(div_le_one hr).mpr ht.2.le⟩)
    rw [smul_smul,div_mul_cancel₀ t hr.ne'] at hh
    exact hh
  · intro hu
    obtain ⟨r,hr,hw⟩ := (hu.and self_mem_nhdsWithin).exists
    exact ⟨r,hw,hr⟩

theorem euclideanLocalDirections_congr_germ {S T : Set ℂ} {x : ℂ}
    (h : ∀ᶠ y in 𝓝 x,y ∈ S ↔ y ∈ T) :
    euclideanLocalDirections S x = euclideanLocalDirections T x := by
  ext u
  have ht : Tendsto (fun r : ℝ => x+r • (u : ℂ)) (𝓝[>] 0) (𝓝 x) := by
    have h0 : Tendsto (fun r : ℝ => x+r • (u : ℂ)) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun r : ℝ => x+r • (u : ℂ)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul,add_zero] using hc.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have he := ht.eventually h
  exact eventually_congr he

/-- The original local angle is the genuine normalized Haar angular size of the actual local region. -/
def euclideanLocalAngle (S : Set ℂ) (x : ℂ) : ℝ :=
  2*Real.pi*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (euclideanLocalDirections S
    x)).toReal

theorem euclideanLocalDirections_univ (x : ℂ) :
    euclideanLocalDirections univ x = univ := by
  ext u
  simp only [euclideanLocalDirections,mem_ofPred_eq,mem_univ,iff_true]
  exact Filter.Eventually.of_forall (fun r => True.intro)

theorem euclideanLocalAngle_of_mem_interior {S : Set ℂ} {x : ℂ} (hx : x ∈ interior S) :
    euclideanLocalAngle S x = 2*Real.pi := by
  have he : ∀ᶠ y in 𝓝 x,y ∈ S ↔ y ∈ (univ : Set ℂ) := by
    filter_upwards [mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset] with y hy
    exact iff_true_intro hy
  unfold euclideanLocalAngle
  rw [euclideanLocalDirections_congr_germ he,euclideanLocalDirections_univ,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure_univ,ENNReal.toReal_one,mul_one]

theorem euclideanLocalDirections_closed_halfPlane (m : ℂ) :
    euclideanLocalDirections {z : ℂ | 0 ≤ inner ℝ z m} 0 =
      {u : Circle | 0 ≤ inner ℝ (u : ℂ) m} := by
  have hc : Convex ℝ {z : ℂ | 0 ≤ inner ℝ z m} := by
    intro a ha b hb r s hr hs hrs
    change 0 ≤ inner ℝ (r • a+s • b) m
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
    exact add_nonneg (mul_nonneg hr ha) (mul_nonneg hs hb)
  rw [← euclideanRayDirections_eq_local hc (by simp)]
  ext u
  constructor
  · rintro ⟨r,hr,hw⟩
    simp only [zero_add,mem_ofPred_eq,real_inner_smul_left] at hw
    exact nonneg_of_mul_nonneg_right hw hr
  · intro hu
    change 0 ≤ inner ℝ (u : ℂ) m at hu
    refine ⟨1,by norm_num,?_⟩
    change 0 ≤ inner ℝ ((0 : ℂ)+ (1 : ℝ) • (u : ℂ)) m
    simpa only [zero_add,one_smul] using hu

theorem euclideanLocalAngle_closed_halfPlane (m : ℂ) (hm : m ≠ 0) :
    euclideanLocalAngle {z : ℂ | 0 ≤ inner ℝ z m} 0 = Real.pi := by
  unfold euclideanLocalAngle
  rw [euclideanLocalDirections_closed_halfPlane m]
  exact polygonDirectionMeasure_hemisphere m hm

theorem euclideanRay_tendsto (x : ℂ) (u : Circle) :
    Tendsto (fun r : ℝ => x+r • (u : ℂ)) (𝓝[>] 0) (𝓝 x) := by
  have hc : Continuous (fun r : ℝ => x+r • (u : ℂ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hh : Tendsto (fun r : ℝ => x+r • (u : ℂ)) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul,add_zero] using hc.tendsto (0 : ℝ)
  exact hh.mono_left nhdsWithin_le_nhds

/-- The actual local directions of a finite closed convex cover are precisely its incident sectors. -/
theorem euclideanLocalDirections_finite_convex_cover {ι : Type*} [Finite ι]
    (S : ι → Set ℂ) (hc : ∀ i,IsClosed (S i)) (hconv : ∀ i,Convex ℝ (S i)) (x : ℂ) :
    euclideanLocalDirections (⋃ i,S i) x =
      ⋃ i ∈ {i | x ∈ S i},euclideanRayDirections (S i) x := by
  ext u
  constructor
  · intro hu
    change ∀ᶠ r in 𝓝[>] (0 : ℝ),x+r • (u : ℂ) ∈ ⋃ i,S i at hu
    have hl := (locallyFinite_of_finite S).iInter_compl_mem_nhds hc x
    have hp := (euclideanRay_tendsto x u).eventually hl
    obtain ⟨r,⟨hrU,hrA⟩,hr⟩ := ((hu.and hp).and self_mem_nhdsWithin).exists
    obtain ⟨i,hi⟩ := mem_iUnion.mp hrU
    have hxi : x ∈ S i := by
      by_contra hn
      exact (mem_iInter₂.mp hrA i hn) hi
    exact mem_iUnion₂.mpr ⟨i,hxi,⟨r,hr,hi⟩⟩
  · intro hu
    obtain ⟨i,hxi,hi⟩ := mem_iUnion₂.mp hu
    have hh : u ∈ euclideanLocalDirections (S i) x :=
      Set.ext_iff.mp (euclideanRayDirections_eq_local (hconv i) hxi) u |>.mp hi
    change ∀ᶠ r in 𝓝[>] (0 : ℝ),x+r • (u : ℂ) ∈ ⋃ i,S i
    filter_upwards [hh] with r hr
    exact mem_iUnion.mpr ⟨i,hr⟩

/-- Disjoint genuine convex planar interiors have only angular-null common directions. -/
theorem finite_euclideanLocalDirections_common_closures {U V : Set ℂ} {x : ℂ}
    (hUc : Convex ℝ U) (hUo : IsOpen U) (hUn : U.Nonempty)
    (hVc : Convex ℝ V) (hVo : IsOpen V) (hVn : V.Nonempty)
    (hd : Disjoint U V) (hxU : x ∈ closure U) (hxV : x ∈ closure V) :
    (euclideanLocalDirections (closure U) x ∩ euclideanLocalDirections (closure V) x).Finite := by
  obtain ⟨m,t,hm,hline⟩ := _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.convex_open_disjoint_closures_hyperplane hUc hUo hUn hVc hVo hVn hd
  have hbase := hline x ⟨hxU,hxV⟩
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.finite_circle_orthogonal m hm).subset
  rintro u ⟨hu,hv⟩
  change ∀ᶠ r in 𝓝[>] (0 : ℝ),x+r • (u : ℂ) ∈ closure U at hu
  change ∀ᶠ r in 𝓝[>] (0 : ℝ),x+r • (u : ℂ) ∈ closure V at hv
  obtain ⟨r,⟨hrU,hrV⟩,hr⟩ := ((hu.and hv).and self_mem_nhdsWithin).exists
  have he := hline (x+r • (u : ℂ)) ⟨hrU,hrV⟩
  rw [inner_add_right,real_inner_smul_right,hbase] at he
  have hzero : inner ℝ m (u : ℂ) = 0 := by
    have hz : r*inner ℝ m (u : ℂ)=0 := by linarith only [he]
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hr)
  change inner ℝ (u : ℂ) m = 0
  rw [real_inner_comm]
  exact hzero

/-- The actual ray directions of a filled Euclidean triangle at its first corner are its genuine nonnegative cone. -/
theorem euclideanRay_triangle_point (a b c w : ℂ) (hw : w ≠ 0) :
    (∃ r : ℝ,0 < r ∧ a+r • w ∈ convexHull ℝ ({a,b,c} : Set ℂ)) ↔
      ∃ s : ℝ,0 ≤ s ∧ ∃ t : ℝ,0 ≤ t ∧ w=s • (b-a)+t • (c-a) := by
  constructor
  · rintro ⟨r,hr,hp⟩
    rw [convexHull_insert (insert_nonempty b {c}),convexHull_pair,convexJoin_singleton_left] at hp
    obtain ⟨y,hy,hyp⟩ := mem_iUnion₂.mp hp
    rw [segment_eq_image_lineMap] at hy hyp
    obtain ⟨t,ht,rfl⟩ := hy
    obtain ⟨s,hs,he⟩ := hyp
    refine ⟨s*(1-t)/r,div_nonneg (mul_nonneg hs.1 (sub_nonneg.mpr ht.2)) hr.le,
      s*t/r,div_nonneg (mul_nonneg hs.1 ht.1) hr.le,?_⟩
    rw [AffineMap.lineMap_apply] at he
    change s • (AffineMap.lineMap b c t-a)+a=a+r • w at he
    rw [add_comm (s • (AffineMap.lineMap b c t-a)) a] at he
    have hh := congrArg (fun w : ℂ => r⁻¹ • w) (add_left_cancel he)
    simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] at hh
    rw [← hh,AffineMap.lineMap_apply]
    simp only [vsub_eq_sub,vadd_eq_add,Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    ring
  · rintro ⟨s,hs,t,ht,hu⟩
    have hsum : 0 < s+t := by
      by_contra hn
      have hs0 : s=0 := by linarith only [not_lt.mp hn,hs,ht]
      have ht0 : t=0 := by linarith only [not_lt.mp hn,hs,ht]
      rw [hs0,ht0,zero_smul,zero_smul,add_zero] at hu
      exact hw hu
    let r : ℝ := 1/(s+t+1)
    have hr : 0 < r := by dsimp [r];positivity
    let y : ℂ := (s/(s+t)) • b+(t/(s+t)) • c
    have hy : y ∈ convexHull ℝ ({a,b,c} : Set ℂ) := by
      apply (convex_convexHull ℝ _) (subset_convexHull ℝ _ (by simp : b ∈ ({a,b,c} : Set ℂ)))
        (subset_convexHull ℝ _ (by simp : c ∈ ({a,b,c} : Set ℂ)))
        (div_nonneg hs hsum.le) (div_nonneg ht hsum.le)
      rw [← add_div,div_self hsum.ne']
    have hcoeff : r*(s+t) ∈ Icc (0 : ℝ) 1 := by
      refine ⟨mul_nonneg hr.le hsum.le,?_⟩
      dsimp [r]
      rw [one_div_mul_eq_div]
      exact (div_le_one (by linarith : 0 < s+t+1)).mpr (by linarith)
    have hmem := (convex_convexHull ℝ ({a,b,c} : Set ℂ)).add_smul_sub_mem
      (subset_convexHull ℝ _ (by simp : a ∈ ({a,b,c} : Set ℂ))) hy hcoeff
    refine ⟨r,hr,?_⟩
    suffices he : a+r • w=a+(r*(s+t)) • (y-a) by rw [he];exact hmem
    rw [hu]
    dsimp [y]
    have hden : (s : ℂ)+(t : ℂ) ≠ 0 := by exact_mod_cast hsum.ne'
    push_cast
    field_simp [hden]
    ring


theorem euclideanRayDirections_triangle (a b c : ℂ) :
    euclideanRayDirections (convexHull ℝ ({a,b,c} : Set ℂ)) a =
      {u : Circle | ∃ s : ℝ,0 ≤ s ∧ ∃ t : ℝ,0 ≤ t ∧
        (u : ℂ)=s • (b-a)+t • (c-a)} := by
  ext u
  exact euclideanRay_triangle_point a b c (u : ℂ) u.coe_ne_zero

/-- The actual Euclidean triangle corner and the standard two-ray angular sector have identical directions. -/
theorem euclideanLocalDirections_triangle (a b c : ℂ) :
    euclideanLocalDirections (convexHull ℝ ({a,b,c} : Set ℂ)) a =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPositiveCone (b-a) (c-a)) := by
  rw [← euclideanRayDirections_eq_local (convex_convexHull ℝ _)
    (subset_convexHull ℝ _ (by simp : a ∈ ({a,b,c} : Set ℂ))),
    euclideanRayDirections_triangle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRadialDirections_positiveCone]
  ext u
  change (∃ s : ℝ,0 ≤ s ∧ ∃ t : ℝ,0 ≤ t ∧ (u : ℂ)=s • (b-a)+t • (c-a)) ↔
    (u : ℂ) ∈ Submodule.span ℝ≥0 {b-a,c-a}
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨s,hs,t,ht,he⟩
    exact ⟨⟨s,hs⟩,⟨t,ht⟩,he.symm⟩
  · rintro ⟨s,t,he⟩
    exact ⟨s,s.property,t,t.property,he.symm⟩

/-- The independent local Jordan-region angular measure equals the ordinary Euclidean corner angle. -/
theorem euclideanLocalAngle_triangle {a b c : ℂ} (hab : b ≠ a) (hac : c ≠ a)
    (hθ : angle (b-a) (c-a) < Real.pi) :
    euclideanLocalAngle (convexHull ℝ ({a,b,c} : Set ℂ)) a = angle (b-a) (c-a) := by
  unfold euclideanLocalAngle
  rw [euclideanLocalDirections_triangle]
  have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_positiveCone (sub_ne_zero.mpr
    hab) (sub_ne_zero.mpr hac) hθ
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngularFraction_zero] at hh
  exact hh

/-- Cofinal actual ray intersections make convex angular directions Borel. -/
theorem euclideanRayDirections_eq_iUnion {S : Set ℂ} {x : ℂ}
    (hc : Convex ℝ S) (hx : x ∈ S) :
    euclideanRayDirections S x = ⋃ n : ℕ,
      (fun u : Circle => x+(1/((n : ℝ)+1)) • (u : ℂ)) ⁻¹' S := by
  ext u
  constructor
  · rintro ⟨r,hr,hp⟩
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hr
    refine mem_iUnion.mpr ⟨n,?_⟩
    have hq : 0 < 1/((n : ℝ)+1) := by positivity
    have hh := hc.add_smul_mem hx hp
      (show (1/((n : ℝ)+1))/r ∈ Icc (0 : ℝ) 1 from
        ⟨div_nonneg hq.le hr.le,(div_le_one hr).mpr hn.le⟩)
    rw [smul_smul,div_mul_cancel₀ _ hr.ne'] at hh
    exact hh
  · intro hu
    obtain ⟨n,hn⟩ := mem_iUnion.mp hu
    exact ⟨1/((n : ℝ)+1),by positivity,hn⟩

theorem measurableSet_euclideanLocalDirections {S : Set ℂ} {x : ℂ}
    (hc : Convex ℝ S) (hClosed : IsClosed S) (hx : x ∈ S) :
    MeasurableSet (euclideanLocalDirections S x) := by
  rw [← euclideanRayDirections_eq_local hc hx,euclideanRayDirections_eq_iUnion hc hx]
  apply MeasurableSet.iUnion
  intro n
  have hU : Continuous (fun u : Circle => (u : ℂ)) := continuous_subtype_val
  have hCont : Continuous (fun u : Circle => x+(1/((n : ℝ)+1)) • (u : ℂ)) := by
    have hB : Continuous (fun u : Circle => x+((1/((n : ℝ)+1) : ℝ) : ℂ)*(u : ℂ)) :=
      continuous_const.add (continuous_const.mul hU)
    have hEq : (fun u : Circle => x+(1/((n : ℝ)+1)) • (u : ℂ)) =
        (fun u : Circle => x+((1/((n : ℝ)+1) : ℝ) : ℂ)*(u : ℂ)) := by
      funext u
      rw [Complex.real_smul]
    exact hEq.symm ▸ hB
  exact (hClosed.preimage hCont).measurableSet

/-- Genuine closed convex face angles add to the actual local angle of their finite union. -/
theorem euclideanLocalAngle_finite_face_sum {ι : Type*} [Fintype ι]
    (S : ι → Set ℂ) (hc : ∀ i,Convex ℝ (S i)) (hClosed : ∀ i,IsClosed (S i))
    (hReg : ∀ i,closure (interior (S i))=S i) (hInt : ∀ i,(interior (S i)).Nonempty)
    (hDis : Pairwise (fun i j => Disjoint (interior (S i)) (interior (S j)))) (x : ℂ) :
    ∑ i ∈ Finset.univ.filter (fun i => x ∈ S i),euclideanLocalAngle (S i) x =
      euclideanLocalAngle (⋃ i,S i) x := by
  let f := fun i => euclideanLocalDirections (S i) x
  let s := Finset.univ.filter (fun i => x ∈ S i)
  have hx (i : ι) (hi : i ∈ s) : x ∈ S i := (Finset.mem_filter.mp hi).2
  have hd : (s : Set ι).Pairwise (fun i j => _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (f i ∩ f j)=0) := by
    intro i hi j hj hij
    have hh := finite_euclideanLocalDirections_common_closures (hc i).interior isOpen_interior (hInt i)
      (hc j).interior isOpen_interior (hInt j) (hDis hij)
      ((hReg i).symm ▸ hx i hi) ((hReg j).symm ▸ hx j hj)
    rw [hReg i,hReg j] at hh
    exact hh.measure_zero _
  have hm := measure_biUnion_finset₀ (μ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure) (s
    := s) (f := f) hd
    (fun i hi => (measurableSet_euclideanLocalDirections (hc i) (hClosed i) (hx i hi)).nullMeasurableSet)
  have hEq : (⋃ i ∈ s,f i)=euclideanLocalDirections (⋃ i,S i) x := by
    rw [euclideanLocalDirections_finite_convex_cover S hClosed hc]
    apply iUnion_congr
    intro i
    by_cases hi : x ∈ S i
    · simp only [s,Finset.mem_filter,Finset.mem_univ,true_and,hi,mem_ofPred_eq,iUnion_true]
      exact euclideanRayDirections_eq_local (hc i) hi |>.symm
    · simp only [s,Finset.mem_filter,Finset.mem_univ,true_and,hi,mem_ofPred_eq,iUnion_false]
  rw [hEq] at hm
  change (∑ i ∈ s,2*Real.pi*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (f i)).toReal) =
    2*Real.pi*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure (euclideanLocalDirections (⋃
      i,S i) x)).toReal
  rw [← Finset.mul_sum,← ENNReal.toReal_sum (fun i hi => measure_ne_top
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.polygonDirectionMeasure _),← hm]

set_option maxHeartbeats 800000 in
theorem euclideanLocalAngle_triangle_of_not_collinear {a b c : ℂ}
    (h : ¬ Collinear ℝ ({a,b,c} : Set ℂ)) :
    euclideanLocalAngle (convexHull ℝ ({a,b,c} : Set ℂ)) a = EuclideanGeometry.angle b a c := by
  have hba : b ≠ a := (ne₁₂_of_not_collinear h).symm
  have hca : c ≠ a := (ne₁₃_of_not_collinear h).symm
  have hset : ({b,a,c} : Set ℂ)=({a,b,c} : Set ℂ) := by
    ext z
    simp only [mem_insert_iff,mem_singleton_iff]
    tauto
  have hswap : ¬ Collinear ℝ ({b,a,c} : Set ℂ) := hset.symm ▸ h
  have hTheta : angle (b-a) (c-a) < Real.pi := by
    simpa only [EuclideanGeometry.angle,vsub_eq_sub] using
      EuclideanGeometry.angle_lt_pi_of_not_collinear hswap
  simpa only [EuclideanGeometry.angle,vsub_eq_sub] using euclideanLocalAngle_triangle hba hca hTheta

end
end LowDimensionalTopology.Geometry.Polygon

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The actual complex image of a genuine mesh face. -/
def complexTriangleCarrier (M : TriangleMesh) (t : M.Triangle) : Set ℂ :=
  PolygonalCircle.planeComplexEquiv '' M.triangleCarrier t.1

theorem complexTriangleCarrier_hull (M : TriangleMesh) (t : M.Triangle) :
    M.complexTriangleCarrier t = convexHull ℝ
      ({PolygonalCircle.planeComplexEquiv (M.position (M.orderedVertex t 0)),
        PolygonalCircle.planeComplexEquiv (M.position (M.orderedVertex t 1)),
        PolygonalCircle.planeComplexEquiv (M.position (M.orderedVertex t 2))} : Set ℂ) := by
  let e := PolygonalCircle.planeComplexEquiv
  change e '' convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) = _
  have he : e '' convexHull ℝ (M.position '' (t.1 : Set M.Vertex)) =
      convexHull ℝ (e '' (M.position '' (t.1 : Set M.Vertex))) :=
    e.toLinearEquiv.toAffineEquiv.toAffineMap.image_convexHull _
  rw [he]
  congr 1
  rw [← M.range_orderedVertex t,← range_comp,← range_comp]
  ext z
  simp only [mem_range,mem_insert_iff,mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem complexTriangleCarrier_isClosed (M : TriangleMesh) (t : M.Triangle) :
    IsClosed (M.complexTriangleCarrier t) := by
  apply PolygonalCircle.planeComplexEquiv.toHomeomorph.isClosedMap
  exact (t.1.finite_toSet.image M.position).isClosed_convexHull ℝ

theorem complexTriangleCarrier_convex (M : TriangleMesh) (t : M.Triangle) :
    Convex ℝ (M.complexTriangleCarrier t) := by
  rw [M.complexTriangleCarrier_hull t]
  exact convex_convexHull ℝ _

theorem complexTriangleCarrier_closure_interior (M : TriangleMesh) (t : M.Triangle) :
    closure (interior (M.complexTriangleCarrier t))=M.complexTriangleCarrier t := by
  change closure (interior (PolygonalCircle.planeComplexEquiv.toHomeomorph '' M.triangleCarrier t.1)) = _
  rw [← PolygonalCircle.planeComplexEquiv.toHomeomorph.image_interior,
    ← PolygonalCircle.planeComplexEquiv.toHomeomorph.image_closure,M.closure_interior_triangleCarrier t]
  rfl

theorem complexTriangleCarrier_interior (M : TriangleMesh) (t : M.Triangle) :
    interior (M.complexTriangleCarrier t) =
      PolygonalCircle.planeComplexEquiv '' interior (M.triangleCarrier t.1) :=
  (PolygonalCircle.planeComplexEquiv.toHomeomorph.image_interior _).symm

theorem complexTriangleCarrier_interior_nonempty (M : TriangleMesh) (t : M.Triangle) :
    (interior (M.complexTriangleCarrier t)).Nonempty := by
  rw [M.complexTriangleCarrier_interior t]
  exact (M.interior_triangleCarrier_nonempty t).image _

theorem complexTriangleCarrier_interior_disjoint (M : TriangleMesh) :
    Pairwise (fun t u : M.Triangle => Disjoint (interior (M.complexTriangleCarrier t))
      (interior (M.complexTriangleCarrier u))) := by
  intro t u htu
  have hn : t.1 ≠ u.1 := fun h => htu (Subtype.ext h)
  rw [M.complexTriangleCarrier_interior t,M.complexTriangleCarrier_interior u]
  exact (M.disjoint_interior_triangleCarrier hn).image PolygonalCircle.planeComplexEquiv.injective.injOn
    (subset_univ _) (subset_univ _)

theorem complex_ordered_not_collinear (M : TriangleMesh) (t : M.Triangle) :
    ¬ Collinear ℝ ({PolygonalCircle.planeComplexEquiv (M.position (M.orderedVertex t 0)),
      PolygonalCircle.planeComplexEquiv (M.position (M.orderedVertex t 1)),
      PolygonalCircle.planeComplexEquiv (M.position (M.orderedVertex t 2))} : Set ℂ) := by
  let e := PolygonalCircle.planeComplexEquiv
  have hAI := (M.orderedVertex_affineIndependent t).map'
    e.toLinearEquiv.toAffineEquiv.toAffineMap e.injective
  have hNot := affineIndependent_iff_not_collinear.mp hAI
  have hRange : range (fun i : Fin 3 => e (M.position (M.orderedVertex t i))) =
      ({e (M.position (M.orderedVertex t 0)),e (M.position (M.orderedVertex t 1)),
        e (M.position (M.orderedVertex t 2))} : Set ℂ) := by
    ext z
    simp only [mem_range,mem_insert_iff,mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
  rw [← hRange]
  exact hNot

/-- Each actual Euclidean mesh corner is the angle of the original filled face germ. -/
theorem complexTriangleCarrier_angle (M : TriangleMesh) (t : M.Triangle) (i : Fin 3) :
    _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (M.complexTriangleCarrier t)
      (PolygonalCircle.planeComplexEquiv (M.position (M.orderedVertex t i))) = M.euclideanCornerAngle t i := by
  let e := PolygonalCircle.planeComplexEquiv
  let p := fun i : Fin 3 => M.position (M.orderedVertex t i)
  let a := e (p 0)
  let b := e (p 1)
  let c := e (p 2)
  have hh : M.complexTriangleCarrier t=convexHull ℝ ({a,b,c} : Set ℂ) := M.complexTriangleCarrier_hull t
  have hn : ¬ Collinear ℝ ({a,b,c} : Set ℂ) := M.complex_ordered_not_collinear t
  have hbc : ({a,b,c} : Set ℂ)=({b,c,a} : Set ℂ) := by
    ext z
    simp only [mem_insert_iff,mem_singleton_iff]
    tauto
  have hca : ({a,b,c} : Set ℂ)=({c,a,b} : Set ℂ) := by
    ext z
    simp only [mem_insert_iff,mem_singleton_iff]
    tauto
  fin_cases i
  · change _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (M.complexTriangleCarrier
    t) a=EuclideanGeometry.angle (p 1) (p 0) (p 2)
    rw [hh,_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle_triangle_of_not_collinear hn]
    exact e.toAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  · change _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (M.complexTriangleCarrier
    t) b=EuclideanGeometry.angle (p 2) (p 1) (p 0)
    have hn' : ¬ Collinear ℝ ({b,c,a} : Set ℂ) := hbc ▸ hn
    rw [hh,hbc,_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle_triangle_of_not_collinear hn']
    exact e.toAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  · change _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (M.complexTriangleCarrier
    t) c=EuclideanGeometry.angle (p 0) (p 2) (p 1)
    have hn' : ¬ Collinear ℝ ({c,a,b} : Set ℂ) := hca ▸ hn
    rw [hh,hca,_root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle_triangle_of_not_collinear hn']
    exact e.toAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _

theorem complexTriangleCarrier_iUnion (M : TriangleMesh) :
    (⋃ t : M.Triangle,M.complexTriangleCarrier t) =
      PolygonalCircle.planeComplexEquiv '' M.toPlaneComplex.support := by
  rw [M.toPlaneComplex_support,image_iUnion]
  simp_rw [image_iUnion]
  ext z
  simp only [mem_iUnion,complexTriangleCarrier]
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t.1,t.2,ht⟩
  · rintro ⟨t,ht,hz⟩
    exact ⟨⟨t,ht⟩,hz⟩

theorem complexTriangleCarrier_mem_usedVertex_iff (M : TriangleMesh)
    (v : {v : M.Vertex // v ∈ M.usedVertices}) (t : M.Triangle) :
    PolygonalCircle.planeComplexEquiv (M.position v.1) ∈ M.complexTriangleCarrier t ↔ v.1 ∈ t.1 := by
  change PolygonalCircle.planeComplexEquiv (M.position v.1) ∈
    PolygonalCircle.planeComplexEquiv '' M.triangleCarrier t.1 ↔ _
  rw [PolygonalCircle.planeComplexEquiv.injective.mem_set_image]
  constructor
  · exact M.mem_triangle_of_position_mem v.2 t.2
  · intro hvt
    exact subset_convexHull ℝ _ ⟨v.1,hvt,rfl⟩

theorem complexTriangleCarrier_angle_of_used_vertex (M : TriangleMesh)
    (v : {v : M.Vertex // v ∈ M.usedVertices}) (t : M.Triangle) (hvt : v.1 ∈ t.1) :
    (∑ i : Fin 3,if M.orderedVertex t i=v.1 then M.euclideanCornerAngle t i else 0) =
      _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (M.complexTriangleCarrier t) (PolygonalCircle.planeComplexEquiv (M.position v.1)) := by
  have hi : v.1 ∈ range (M.orderedVertex t) := by rw [M.range_orderedVertex t];exact hvt
  obtain ⟨i,hi⟩ := hi
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left hi,← hi]
    exact (M.complexTriangleCarrier_angle t i).symm
  · intro j hj hji
    apply ite_eq_right
    intro he
    exact hji ((M.orderedVertex_injective t) (he.trans hi.symm))
  · exact fun hn => (hn (Finset.mem_univ _)).elim

/-- The incident Euclidean mesh angle is the angular measure of the actual closed support germ. -/
theorem euclideanAngleSumAt_eq_localAngle (M : TriangleMesh)
    (v : {v : M.Vertex // v ∈ M.usedVertices}) :
    M.euclideanAngleSumAt v = _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle
      (PolygonalCircle.planeComplexEquiv '' M.toPlaneComplex.support)
      (PolygonalCircle.planeComplexEquiv (M.position v.1)) := by
  have hh := _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle_finite_face_sum (fun t : M.Triangle =>
    M.complexTriangleCarrier t)
    M.complexTriangleCarrier_convex M.complexTriangleCarrier_isClosed
    M.complexTriangleCarrier_closure_interior M.complexTriangleCarrier_interior_nonempty
    M.complexTriangleCarrier_interior_disjoint (PolygonalCircle.planeComplexEquiv (M.position v.1))
  rw [M.complexTriangleCarrier_iUnion] at hh
  refine Eq.trans ?_ hh
  rw [Finset.sum_filter]
  unfold euclideanAngleSumAt
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hvt : v.1 ∈ t.1
  · rw [ite_eq_left ((M.complexTriangleCarrier_mem_usedVertex_iff v t).mpr hvt)]
    exact M.complexTriangleCarrier_angle_of_used_vertex v t hvt
  · rw [ite_eq_right (fun h => hvt ((M.complexTriangleCarrier_mem_usedVertex_iff v t).mp h))]
    apply Finset.sum_eq_zero
    intro i hi
    apply ite_eq_right
    intro he
    exact hvt (he ▸ M.orderedVertex_mem t i)

end
end LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh

namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

theorem closure_euclidean_open_halfPlane_zero (m : ℂ) (hm : m ≠ 0) :
    closure {z : ℂ | 0 < inner ℝ z m}={z : ℂ | 0 ≤ inner ℝ z m} := by
  let f : ℂ →L[ℝ] ℝ := innerSL ℝ m
  have hf : Function.Surjective f := by
    intro r
    refine ⟨(r/‖m‖^2) • m,?_⟩
    change inner ℝ m ((r/‖m‖^2) • m)=r
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ r (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  have hOpen : {z : ℂ | 0 < inner ℝ z m}=f ⁻¹' Ioi 0 := by
    ext z
    change 0 < inner ℝ z m ↔ 0 < inner ℝ m z
    rw [real_inner_comm]
  have hClosed : {z : ℂ | 0 ≤ inner ℝ z m}=f ⁻¹' Ici 0 := by
    ext z
    change 0 ≤ inner ℝ z m ↔ 0 ≤ inner ℝ m z
    rw [real_inner_comm]
  rw [hOpen,hClosed,← (f.isOpenMap hf).preimage_closure_eq_closure_preimage f.continuous,closure_Ioi]

theorem closure_euclidean_open_halfPlane (x m : ℂ) (hm : m ≠ 0) :
    closure {z : ℂ | 0 < inner ℝ (z-x) m}={z : ℂ | 0 ≤ inner ℝ (z-x) m} := by
  let h : ℂ ≃ₜ ℂ := (Homeomorph.addRight x).symm
  have hOpen : {z : ℂ | 0 < inner ℝ (z-x) m}=h ⁻¹' {z : ℂ | 0 < inner ℝ z m} := by rfl
  have hClosed : {z : ℂ | 0 ≤ inner ℝ (z-x) m}=h ⁻¹' {z : ℂ | 0 ≤ inner ℝ z m} := by rfl
  rw [hOpen,hClosed,← h.isOpenMap.preimage_closure_eq_closure_preimage h.continuous,
    closure_euclidean_open_halfPlane_zero m hm]

theorem euclideanLocalDirections_translate (S : Set ℂ) (x : ℂ) :
    euclideanLocalDirections ((fun z : ℂ => z-x) ⁻¹' S) x=euclideanLocalDirections S 0 := by
  ext u
  change (∀ᶠ r in 𝓝[>] (0 : ℝ),(x+r • (u : ℂ)-x) ∈ S) ↔
    ∀ᶠ r in 𝓝[>] (0 : ℝ),(0 : ℂ)+r • (u : ℂ) ∈ S
  apply Filter.eventually_congr
  filter_upwards [] with r
  rw [add_sub_cancel_left,zero_add]

theorem euclideanLocalAngle_halfPlane_at (x m : ℂ) (hm : m ≠ 0) :
    euclideanLocalAngle {z : ℂ | 0 ≤ inner ℝ (z-x) m} x=Real.pi := by
  have he : euclideanLocalDirections {z : ℂ | 0 ≤ inner ℝ (z-x) m} x=
      euclideanLocalDirections {z : ℂ | 0 ≤ inner ℝ z m} 0 :=
    euclideanLocalDirections_translate {z : ℂ | 0 ≤ inner ℝ z m} x
  unfold euclideanLocalAngle
  rw [he]
  exact euclideanLocalAngle_closed_halfPlane m hm

/-- A genuine two-sided Jordan straight-line germ has its actual Euclidean interior angle pi. -/
theorem euclideanLocalAngle_of_jordan_line {I O B : Set ℂ} {x : ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O)
    (hu : ∀ᶠ y in 𝓝 x,(y ∈ I ∨ y ∈ O) ↔ y ∉ B)
    (hxI : x ∈ frontier I) (hxO : x ∈ frontier O)
    (m : ℂ) (hm : m ≠ 0)
    (hB : ∀ᶠ y in 𝓝 x,y ∈ B ↔ inner ℝ (y-x) m=0) :
    euclideanLocalAngle (closure I) x=Real.pi := by
  let f : ℂ →ᵃ[ℝ] ℝ := (innerSL ℝ m).toLinearMap.toAffineMap.comp
    (AffineEquiv.vaddConst ℝ x).symm.toAffineMap
  have hf (y : ℂ) : f y=inner ℝ (y-x) m := by
    change inner ℝ m (y-x)=inner ℝ (y-x) m
    rw [real_inner_comm]
  have hLine : ∀ᶠ y in 𝓝 x,y ∈ B ↔ f y=0 := by
    filter_upwards [hB] with y hy
    rw [hf]
    exact hy
  have hp := complex_jordan_linear_boundary_halfplane_germ hI hO hd hu hxI hxO f hLine
  have hSide : ∃ n : ℂ,n ≠ 0 ∧ ∀ᶠ y in 𝓝 x,y ∈ I ↔ 0 < inner ℝ (y-x) n := by
    rcases hp with hp | hn
    · refine ⟨m,hm,?_⟩
      filter_upwards [hp] with y hy
      exact hy.trans (by rw [hf])
    · refine ⟨-m,neg_ne_zero.mpr hm,?_⟩
      filter_upwards [hn] with y hy
      exact hy.trans (by rw [hf,inner_neg_right,neg_pos])
  obtain ⟨n,hn,hG⟩ := hSide
  have hc := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hG
  have he : ∀ᶠ y in 𝓝 x,y ∈ closure I ↔ 0 ≤ inner ℝ (y-x) n := by
    filter_upwards [hc] with y hy
    exact hy.trans (Set.ext_iff.mp (closure_euclidean_open_halfPlane x n hn) y)
  unfold euclideanLocalAngle
  rw [euclideanLocalDirections_congr_germ he]
  exact euclideanLocalAngle_halfPlane_at x n hn

theorem euclideanLocalAngle_of_jordan_affineLine {I O B : Set ℂ} {x a b : ℂ}
    (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O)
    (hu : ∀ᶠ y in 𝓝 x,(y ∈ I ∨ y ∈ O) ↔ y ∉ B)
    (hxI : x ∈ frontier I) (hxO : x ∈ frontier O) (hxB : x ∈ B) (hab : a ≠ b)
    (hB : ∀ᶠ y in 𝓝 x,y ∈ B ↔ polygonComplexLineEquation a b y=0) :
    euclideanLocalAngle (closure I) x=Real.pi := by
  let m := Complex.I*(b-a)
  have hm : m ≠ 0 := mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hab.symm)
  have hOrth : inner ℝ m (b-a)=0 := by
    have hh := real_inner_I_smul_self (𝕜 := ℂ) (b-a)
    change inner ℝ (b-a) (Complex.I*(b-a))=0 at hh
    rw [real_inner_comm]
    exact hh
  have hb : inner ℝ m b=inner ℝ m a := by
    rw [inner_sub_right] at hOrth
    linarith only [hOrth]
  have hxb := (hB.self_of_nhds).mp hxB
  have hx : inner ℝ m x=inner ℝ m a :=
    (complex_lineEquation_eq_zero_iff hab hm rfl hb).mpr hxb
  have hLine : ∀ᶠ y in 𝓝 x,y ∈ B ↔ inner ℝ (y-x) m=0 := by
    filter_upwards [hB] with y hy
    rw [real_inner_comm,inner_sub_right,hx,sub_eq_zero]
    exact hy.trans (complex_lineEquation_eq_zero_iff hab hm rfl hb).symm
  exact euclideanLocalAngle_of_jordan_line hI hO hd hu hxI hxO m hm hLine

end
end LowDimensionalTopology.Geometry.Polygon

namespace LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- The actual Euclidean interior angle, measured solely from the original closed Jordan region germ. -/
def euclideanInteriorAngle (J : PolygonalCircle) (i : ZMod J.n) : ℝ :=
  _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (planeComplexEquiv ''
    J.closedRegion) (planeComplexEquiv (J.vertex i))

/-- Any genuine local line on the original Jordan boundary determines a straight Euclidean angle. -/
theorem euclideanLocalAngle_of_carrier_line (J : PolygonalCircle) {x : Plane}
    (hx : x ∈ J.carrier) {a b : ℂ} (hab : a ≠ b)
    (hB : ∀ᶠ y in 𝓝 (planeComplexEquiv x),
      y ∈ planeComplexEquiv '' J.carrier ↔ _root_.LowDimensionalTopology.Geometry.Polygon.polygonComplexLineEquation a b y=0) :
    _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (planeComplexEquiv '' J.closedRegion) (planeComplexEquiv x)=Real.pi := by
  let e := planeComplexEquiv.toHomeomorph
  let I := e '' J.interiorRegion
  let O := e '' J.exteriorRegion
  let B := e '' J.carrier
  have hu : I ∪ O=Bᶜ := by
    rw [← image_union,J.interior_union_exterior,image_compl_eq e.bijective]
  have hxI : e x ∈ frontier I := by
    rw [← e.image_frontier,J.frontier_interiorRegion]
    exact mem_image_of_mem e hx
  have hxO : e x ∈ frontier O := by
    rw [← e.image_frontier,J.frontier_exteriorRegion]
    exact mem_image_of_mem e hx
  have hPartition : ∀ᶠ y in 𝓝 (e x),(y ∈ I ∨ y ∈ O) ↔ y ∉ B := by
    apply Filter.Eventually.of_forall
    intro y
    exact Set.ext_iff.mp hu y
  have hh := _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle_of_jordan_affineLine (e.isOpenMap _
    J.isOpen_interiorRegion)
    (e.isOpenMap _ J.isOpen_exteriorRegion)
    (J.disjoint_interior_exterior.image e.injective.injOn (subset_univ _) (subset_univ _))
    hPartition hxI hxO (mem_image_of_mem e hx) hab hB
  have he : planeComplexEquiv '' J.closedRegion=closure I := by
    exact e.image_closure J.interiorRegion
  rw [he]
  exact hh

theorem previous_next_vertices_ne (J : PolygonalCircle) (i : ZMod J.n) :
    J.vertex (i-1) ≠ J.vertex (i+1) := by
  intro he
  apply J.outgoingDirection_ne_incomingRayDirection i
  have hv : J.outgoingVector i=J.incomingRayVector i := by
    rw [outgoingVector,incomingRayVector,he]
  simp only [outgoingDirection,incomingRayDirection,hv]

theorem euclideanInteriorAngle_of_collinear (J : PolygonalCircle) (i : ZMod J.n)
    (hc : Collinear ℝ ({J.vertex (i-1),J.vertex i,J.vertex (i+1)} : Set Plane)) :
    J.euclideanInteriorAngle i=Real.pi := by
  exact J.euclideanLocalAngle_of_carrier_line (J.vertex_mem_carrier i)
    (planeComplexEquiv.injective.ne (J.previous_next_vertices_ne i))
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonalCircle_complex_carrier_straight_germ J i hc)

/-- Omitting a genuine original vertex from the derived mesh can only remove a straight angle. -/
theorem euclideanInteriorAngle_of_not_used (J : PolygonalCircle) (i : ZMod J.n)
    (hv : ∀ v ∈ J.closedRegionMesh.usedVertices,J.closedRegionMesh.position v ≠ J.vertex i) :
    J.euclideanInteriorAngle i=Real.pi := by
  let M := J.closedRegionMesh
  have hp : J.vertex i ∈ frontier M.toPlaneComplex.support := by
    rw [J.closedRegionMesh_support,J.frontier_closedRegion]
    exact J.vertex_mem_carrier i
  have hNo : ∀ v ∈ M.usedVertices,J.vertex i ≠ M.position v :=
    fun v hused => (hv v hused).symm
  obtain ⟨a,b,hab,hs,hi⟩ := _root_.LowDimensionalTopology.Geometry.Polygon.mesh_frontier_open_boundaryEdge M hp hNo
  rw [J.closedRegionMesh_support,J.frontier_closedRegion] at hs
  exact J.euclideanInteriorAngle_of_collinear i
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonalCircle_collinear_of_boundary_openSegment J i
      (M.position_injective.ne hab) hs hi)

theorem euclideanLocalAngle_of_nonvertex_carrier (J : PolygonalCircle) {x : Plane}
    (hx : x ∈ J.carrier) (hv : ∀ i : ZMod J.n,x ≠ J.vertex i) :
    _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle (planeComplexEquiv '' J.closedRegion) (planeComplexEquiv x)=Real.pi := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  have hOpen : x ∈ openSegment ℝ (J.vertex i) (J.vertex (i+1)) :=
    mem_openSegment_of_ne_left_right (hv i).symm (hv (i+1)).symm hi
  have hComplex : planeComplexEquiv x ∈ openSegment ℝ
      (planeComplexEquiv (J.vertex i)) (planeComplexEquiv (J.vertex (i+1))) := by
    have hh := mem_image_of_mem planeComplexEquiv hOpen
    have he : planeComplexEquiv '' openSegment ℝ (J.vertex i) (J.vertex (i+1)) =
        openSegment ℝ (planeComplexEquiv (J.vertex i)) (planeComplexEquiv (J.vertex (i+1))) :=
      image_openSegment ℝ planeComplexEquiv.toLinearEquiv.toAffineEquiv.toAffineMap _ _
    exact he ▸ hh
  exact J.euclideanLocalAngle_of_carrier_line hx (planeComplexEquiv.injective.ne (J.adjacent_ne i))
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonalCircle_complex_carrier_line_germ J i hComplex)

abbrev UsedEuclideanMeshVertex (J : PolygonalCircle) :=
  {v : J.closedRegionMesh.Vertex // v ∈ J.closedRegionMesh.usedVertices}

def euclideanMeshBoundaryTurning (J : PolygonalCircle) (v : J.UsedEuclideanMeshVertex) : ℝ :=
  if J.closedRegionMesh.position v.1 ∈ J.carrier then Real.pi-J.closedRegionMesh.euclideanAngleSumAt v else 0

theorem euclideanAngleSumAt_of_original (J : PolygonalCircle)
    (v : J.UsedEuclideanMeshVertex) (i : ZMod J.n) (hv : J.closedRegionMesh.position v.1=J.vertex i) :
    J.closedRegionMesh.euclideanAngleSumAt v=J.euclideanInteriorAngle i := by
  rw [J.closedRegionMesh.euclideanAngleSumAt_eq_localAngle v,J.closedRegionMesh_support,hv]
  rfl

theorem euclideanMeshBoundaryTurning_of_original (J : PolygonalCircle)
    (v : J.UsedEuclideanMeshVertex) (i : ZMod J.n) (hv : J.closedRegionMesh.position v.1=J.vertex i) :
    J.euclideanMeshBoundaryTurning v=Real.pi-J.euclideanInteriorAngle i := by
  rw [euclideanMeshBoundaryTurning,ite_eq_left (hv ▸ J.vertex_mem_carrier i),
    J.euclideanAngleSumAt_of_original v i hv]

theorem euclideanMeshBoundaryTurning_of_not_original (J : PolygonalCircle)
    (v : J.UsedEuclideanMeshVertex) (hv : ∀ i : ZMod J.n,J.closedRegionMesh.position v.1 ≠ J.vertex i) :
    J.euclideanMeshBoundaryTurning v=0 := by
  unfold euclideanMeshBoundaryTurning
  split_ifs with hb
  · rw [J.closedRegionMesh.euclideanAngleSumAt_eq_localAngle v,J.closedRegionMesh_support,
      J.euclideanLocalAngle_of_nonvertex_carrier hb hv,sub_self]
  · rfl

theorem sum_euclideanMeshBoundaryTurning (J : PolygonalCircle) :
    ∑ v : J.UsedEuclideanMeshVertex,J.euclideanMeshBoundaryTurning v =
      ∑ i : ZMod J.n,(Real.pi-J.euclideanInteriorAngle i) := by
  symm
  have hExists (i : ZMod J.n) (hi : Real.pi-J.euclideanInteriorAngle i ≠ 0) :
      ∃ v : J.UsedEuclideanMeshVertex,J.closedRegionMesh.position v.1=J.vertex i := by
    by_contra hn
    push Not at hn
    have hNo : ∀ v ∈ J.closedRegionMesh.usedVertices,J.closedRegionMesh.position v ≠ J.vertex i :=
      fun v hv => hn ⟨v,hv⟩
    exact hi (by rw [J.euclideanInteriorAngle_of_not_used i hNo,sub_self])
  let j (i : ZMod J.n) (_ : i ∈ (Finset.univ : Finset (ZMod J.n)))
      (hi : Real.pi-J.euclideanInteriorAngle i ≠ 0) := (hExists i hi).choose
  have hj (i : ZMod J.n) (him : i ∈ (Finset.univ : Finset (ZMod J.n)))
      (hi : Real.pi-J.euclideanInteriorAngle i ≠ 0) :
      J.closedRegionMesh.position (j i him hi).1=J.vertex i := (hExists i hi).choose_spec
  apply Finset.sum_bij_ne_zero j (by intros; exact Finset.mem_univ _)
  · intro i him hi k hkm hk he
    exact J.vertex_injective ((hj i him hi).symm.trans
      ((congrArg (fun v : J.UsedEuclideanMeshVertex => J.closedRegionMesh.position v.1) he).trans
        (hj k hkm hk)))
  · intro v hvm hv
    have ho : ∃ i : ZMod J.n,J.closedRegionMesh.position v.1=J.vertex i := by
      by_contra hn
      push Not at hn
      exact hv (J.euclideanMeshBoundaryTurning_of_not_original v hn)
    obtain ⟨i,hi⟩ := ho
    have hnon : Real.pi-J.euclideanInteriorAngle i ≠ 0 := by
      rw [← J.euclideanMeshBoundaryTurning_of_original v i hi]
      exact hv
    refine ⟨i,Finset.mem_univ _,hnon,Subtype.ext (J.closedRegionMesh.position_injective ?_)⟩
    exact (hj i (Finset.mem_univ _) hnon).trans hi.symm
  · intro i him hi
    exact (J.euclideanMeshBoundaryTurning_of_original (j i him hi) i (hj i him hi)).symm

theorem euclideanAngleSumAt_of_interior (J : PolygonalCircle)
    (v : J.UsedEuclideanMeshVertex) (hb : J.closedRegionMesh.position v.1 ∉ J.carrier) :
    J.closedRegionMesh.euclideanAngleSumAt v=2*Real.pi := by
  have hp : J.closedRegionMesh.position v.1 ∈ J.closedRegion := by
    rw [← J.closedRegionMesh_support,J.closedRegionMesh.toPlaneComplex_support]
    obtain ⟨t,ht,hvt⟩ := J.closedRegionMesh.mem_usedVertices.mp v.2
    exact mem_iUnion₂.mpr ⟨t,ht,subset_convexHull ℝ _ ⟨v.1,hvt,rfl⟩⟩
  rw [J.closedRegion_eq_union] at hp
  have hx : J.closedRegionMesh.position v.1 ∈ interior J.closedRegion := by
    rw [J.interior_closedRegion]
    exact hp.resolve_right hb
  have hComplex : planeComplexEquiv (J.closedRegionMesh.position v.1) ∈
      interior (planeComplexEquiv '' J.closedRegion) := by
    have he : interior (planeComplexEquiv '' J.closedRegion)=
        planeComplexEquiv '' interior J.closedRegion :=
      (planeComplexEquiv.toHomeomorph.image_interior _).symm
    rw [he]
    exact mem_image_of_mem _ hx
  rw [J.closedRegionMesh.euclideanAngleSumAt_eq_localAngle v,J.closedRegionMesh_support]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.euclideanLocalAngle_of_mem_interior hComplex

theorem sum_euclideanBoundaryIndicator (J : PolygonalCircle) :
    (∑ v : J.UsedEuclideanMeshVertex,
      if J.closedRegionMesh.position v.1 ∈ J.carrier then Real.pi else 0) =
      J.closedRegionMesh.boundaryVertices.card*Real.pi := by
  let M := J.closedRegionMesh
  have hMem (v : J.UsedEuclideanMeshVertex) :
      M.position v.1 ∈ J.carrier ↔ v.1 ∈ M.boundaryVertices := by
    rw [TriangleMesh.boundaryVertices,Finset.mem_filter]
    constructor
    · intro hp
      refine ⟨v.property,?_⟩
      rw [J.closedRegionMesh_support,J.frontier_closedRegion]
      exact hp
    · rintro ⟨hv,hp⟩
      rw [J.closedRegionMesh_support,J.frontier_closedRegion] at hp
      exact hp
  have hs := Finset.sum_subtype (F := inferInstance)
    (p := fun v : M.Vertex => v ∈ M.usedVertices) M.usedVertices (by intro v; rfl)
    (fun v : M.Vertex => if v ∈ M.boundaryVertices then Real.pi else 0)
  have hPoint : (∑ v : J.UsedEuclideanMeshVertex,if M.position v.1 ∈ J.carrier then Real.pi else 0) =
      ∑ v : J.UsedEuclideanMeshVertex,if v.1 ∈ M.boundaryVertices then Real.pi else 0 := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [hMem v]
    by_cases hb : v.1 ∈ M.boundaryVertices
    · rw [ite_eq_left hb,ite_eq_left hb]
    · rw [ite_eq_right hb,ite_eq_right hb]
  rw [hPoint,← hs]
  have hfilter : M.usedVertices.filter (fun v => v ∈ M.boundaryVertices)=M.boundaryVertices := by
    ext v
    simp only [Finset.mem_filter,TriangleMesh.boundaryVertices]
    tauto
  rw [← Finset.sum_filter,hfilter]
  simp
  rfl

/-- The actual Euclidean interior angles of every genuine Jordan polygon have the original total. -/
theorem euclideanInteriorAngle_sum (J : PolygonalCircle) :
    ∑ i : ZMod J.n,J.euclideanInteriorAngle i=((J.n : ℝ)-2)*Real.pi := by
  let M := J.closedRegionMesh
  have hEuler := M.boundaryDiskCharacteristic_of_polygonalDisk J J.closedRegionMesh_support
  unfold TriangleMesh.boundaryDiskCharacteristic at hEuler
  have hER : 2*(M.usedVertices.card : ℝ)-(M.triangles.card : ℝ)-(M.boundaryVertices.card : ℝ)=2 := by
    exact_mod_cast hEuler
  have hV : (Fintype.card J.UsedEuclideanMeshVertex : ℝ)=(M.usedVertices.card : ℝ) := by
    norm_cast
    exact Fintype.card_coe M.usedVertices
  have hPoint (v : J.UsedEuclideanMeshVertex) :
      M.euclideanAngleSumAt v+J.euclideanMeshBoundaryTurning v =
        2*Real.pi-(if M.position v.1 ∈ J.carrier then Real.pi else 0) := by
    by_cases hb : M.position v.1 ∈ J.carrier
    · rw [euclideanMeshBoundaryTurning,ite_eq_left hb,ite_eq_left hb]
      ring
    · rw [euclideanMeshBoundaryTurning,ite_eq_right hb,ite_eq_right hb,
        J.euclideanAngleSumAt_of_interior v hb]
      ring
  have hSum := Finset.sum_congr (s₁ := (Finset.univ : Finset J.UsedEuclideanMeshVertex)) rfl
    (fun v hv => hPoint v)
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,M.sum_euclideanAngleSumAt,
    J.sum_euclideanMeshBoundaryTurning,J.sum_euclideanBoundaryIndicator] at hSum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_sub_distrib,
    ZMod.card] at hSum
  rw [hV] at hSum
  have hEpi := congrArg (fun r : ℝ => r*Real.pi) hER
  nlinarith only [hSum,hEpi]

/-- The independently determined Euclidean interior angles give total exterior turning two pi. -/
theorem euclideanTurning_sum (J : PolygonalCircle) :
    ∑ i : ZMod J.n,(Real.pi-J.euclideanInteriorAngle i)=2*Real.pi := by
  rw [Finset.sum_sub_distrib,J.euclideanInteriorAngle_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,ZMod.card]
  ring

end
end LeanEval.Topology.ClassificationOfSurfaces.Moise.PolygonalCircle
