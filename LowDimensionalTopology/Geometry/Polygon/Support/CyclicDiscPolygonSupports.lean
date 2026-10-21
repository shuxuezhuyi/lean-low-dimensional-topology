/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Polygon.Support.CenteredDiscPolygonSupports
public import Mathlib.Data.Finset.Max
/-! # Actual cyclic supports construct a genuine convex Jordan polygon

The supplied data are actual cyclic closed-disc vertices and genuine affine supporting
half-planes, with strict nonincident support positions. A maximal-functional argument
proves the entire support body lies in the Klein disc; the average vertex is strictly
feasible. Neither a bounded body, an interior center, a Jordan curve nor an angle
conclusion is assumed.
-/
@[expose] public section
open Set InnerProductGeometry
open scoped Complex.UnitDisc Topology
namespace LowDimensionalTopology.Geometry.Polygon
noncomputable section

/-- True cyclic supporting lines and vertices; no center, bounded-body, Jordan or angle conclusion is supplied. -/
structure CyclicDiscPolygonSupportData (n : ℕ) where
  three_le : 3≤n
  vertices : Fin n → 𝕔𝔻
  vertices_injective : Function.Injective vertices
  normals : Fin n → ℂ
  normal_norm : ∀ i,‖normals i‖=1
  offsets : Fin n → ℝ
  incident : ∀ i,inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices
    i))=offsets i ∧
    inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices (finRotate n
      i)))=offsets i
  nonincident : ∀ i j,j≠i → j≠finRotate n i →
    inner ℝ (normals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (vertices j))<offsets i

/-- A linear functional maximal at a vertex is in the positive cone of its two adjacent genuine support normals. -/
theorem CyclicDiscPolygonSupportData.maximal_functional_nonnegative_normals {n : ℕ}
    (S : CyclicDiscPolygonSupportData n) (z : ℂ) (i : Fin n)
    (hmax : ∀ j : Fin n,inner ℝ z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
      j))≤
      inner ℝ z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i))) :
    ∃ a b : ℝ,0≤a ∧ 0≤b ∧ z=a • S.normals ((finRotate n).symm i)+b • S.normals i := by
  let prev := (finRotate n).symm i
  let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)
  let q := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i))
  let r := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices prev)
  let u := q-p
  let v := r-p
  have hprev : finRotate n prev=i := (finRotate n).apply_symm_apply i
  have hprevp : inner ℝ (S.normals prev) p=S.offsets prev := by simpa only [hprev] using (S.incident prev).2
  have hprevq : inner ℝ (S.normals prev) q<S.offsets prev := S.nonincident prev (finRotate n i)
    (centeredPolygonSupport_prev_ne_next S.three_le i).symm
    (by rw [hprev];exact centeredPolygonSupport_next_ne_self S.three_le i)
  have hiv : inner ℝ (S.normals i) v<0 := by
    change inner ℝ (S.normals i) (r-p)<0
    rw [inner_sub_right,(S.incident i).1]
    exact sub_neg.mpr (S.nonincident i prev (centeredPolygonSupport_prev_ne_self S.three_le i)
      (centeredPolygonSupport_prev_ne_next S.three_le i))
  have hpu : inner ℝ (S.normals prev) u<0 := by
    change inner ℝ (S.normals prev) (q-p)<0
    rw [inner_sub_right,hprevp]
    exact sub_neg.mpr hprevq
  have hiu : inner ℝ (S.normals i) u=0 := by
    change inner ℝ (S.normals i) (q-p)=0
    rw [inner_sub_right,(S.incident i).1,(S.incident i).2,sub_self]
  have hpv : inner ℝ (S.normals prev) v=0 := by
    change inner ℝ (S.normals prev) (r-p)=0
    rw [inner_sub_right,(S.incident prev).1,hprevp,sub_self]
  have hzu : inner ℝ z u≤0 := by
    change inner ℝ z (q-p)≤0
    rw [inner_sub_right]
    exact sub_nonpos.mpr (hmax (finRotate n i))
  have hzv : inner ℝ z v≤0 := by
    change inner ℝ z (r-p)≤0
    rw [inner_sub_right]
    exact sub_nonpos.mpr (hmax prev)
  let a := inner ℝ z u/inner ℝ (S.normals prev) u
  let b := inner ℝ z v/inner ℝ (S.normals i) v
  have ha : 0≤a := div_nonneg_of_nonpos hzu hpu.le
  have hb : 0≤b := div_nonneg_of_nonpos hzv hiv.le
  have hau : a*inner ℝ (S.normals prev) u=inner ℝ z u := div_mul_cancel₀ _ hpu.ne
  have hbv : b*inner ℝ (S.normals i) v=inner ℝ z v := div_mul_cancel₀ _ hiv.ne
  let w := z-a • S.normals prev-b • S.normals i
  have hwu : inner ℝ w u=0 := by
    change inner ℝ (z-a • S.normals prev-b • S.normals i) u=0
    rw [inner_sub_left,inner_sub_left,real_inner_smul_left,real_inner_smul_left,hiu,hau]
    ring
  have hwv : inner ℝ w v=0 := by
    change inner ℝ (z-a • S.normals prev-b • S.normals i) v=0
    rw [inner_sub_left,inner_sub_left,real_inner_smul_left,real_inner_smul_left,hpv,hbv]
    ring
  have hw : w=0 := by
    by_contra hne
    have hn : S.normals i≠0 := by intro he;have hh:=S.normal_norm i;rw [he,norm_zero] at hh;norm_num at hh
    have hpq : p≠q := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne
      (S.vertices_injective.ne (centeredPolygonSupport_next_ne_self S.three_le i).symm)
    have hwq : inner ℝ w q=inner ℝ w p := by
      change inner ℝ w (q-p)=0 at hwu
      rw [inner_sub_right] at hwu
      exact sub_eq_zero.mp hwu
    obtain ⟨k,hk,hkw,_⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_affine_normals_proportional (S.normals i) w p q
      (S.offsets i) (inner ℝ w p) hn hne hpq (S.incident i).1 (S.incident i).2 rfl hwq
    rw [hkw,real_inner_smul_left] at hwv
    exact (mul_ne_zero hk hiv.ne) hwv
  refine ⟨a,b,ha,hb,?_⟩
  calc
    z = (z-a • S.normals prev-b • S.normals i)+a • S.normals prev+b • S.normals i := by abel
    _ = a • S.normals prev+b • S.normals i := by change w+_+_=_;rw [hw,zero_add]

/-- The true support intersection lies in the closed Klein disc; this is derived from the cyclic geometry. -/
theorem CyclicDiscPolygonSupportData.region_subset_closedBall {n : ℕ} (S : CyclicDiscPolygonSupportData n) :
    {z : ℂ | ∀ i,inner ℝ (S.normals i) z≤S.offsets i} ⊆ Metric.closedBall 0 1 := by
  intro z hz
  change dist z 0≤1
  rw [dist_zero_right]
  by_contra hnot
  have hn : 1<‖z‖ := lt_of_not_ge hnot
  obtain ⟨i,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => inner ℝ z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices
      i)))
    ⟨⟨0,by have h:=S.three_le;omega⟩,Finset.mem_univ _⟩
  obtain ⟨a,b,ha,hb,hvec⟩ := S.maximal_functional_nonnegative_normals z i (fun j=>hmax j (Finset.mem_univ j))
  let prev := (finRotate n).symm i
  let p := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)
  have hprev : finRotate n prev=i := (finRotate n).apply_symm_apply i
  have hprevp : inner ℝ (S.normals prev) p=S.offsets prev := by simpa only [hprev] using (S.incident prev).2
  have hbound : inner ℝ z z≤ inner ℝ z p := by
    calc
      inner ℝ z z = inner ℝ (a • S.normals prev+b • S.normals i) z :=
        congrArg (fun x : ℂ=>inner ℝ x z) hvec
      _ = a*inner ℝ (S.normals prev) z+b*inner ℝ (S.normals i) z := by
        rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
      _ ≤ a*S.offsets prev+b*S.offsets i := add_le_add
        (mul_le_mul_of_nonneg_left (hz prev) ha) (mul_le_mul_of_nonneg_left (hz i) hb)
      _ = inner ℝ z p := by rw [hvec,inner_add_left,real_inner_smul_left,real_inner_smul_left,hprevp,(S.incident i).1]
  have hp : ‖p‖≤1 := by
    have h : p∈Metric.closedBall (0 :
      ℂ) 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.range_closedKleinCoordinate ▸ mem_range_self (S.vertices
      i)
    simpa only [Metric.mem_closedBall,dist_zero_right] using h
  rw [real_inner_self_eq_norm_sq] at hbound
  have hnorm := real_inner_le_norm z p
  have hprod : ‖z‖*‖p‖≤‖z‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg z)
  nlinarith only [hbound,hnorm,hprod,hn]


def CyclicDiscPolygonSupportData.center {n : ℕ} (S : CyclicDiscPolygonSupportData n) : ℂ :=
  (n : ℝ)⁻¹ • ∑ i : Fin n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)

/-- The average of the genuine cyclic vertices is strictly inside every actual support. -/
theorem CyclicDiscPolygonSupportData.center_strict {n : ℕ} (S : CyclicDiscPolygonSupportData n) (i : Fin n) :
    inner ℝ (S.normals i) S.center<S.offsets i := by
  have hn : 0<(n : ℝ) := by exact_mod_cast (by have h:=S.three_le;omega : 0<n)
  have hle : ∀ j∈(Finset.univ : Finset (Fin n)),inner ℝ (S.normals i)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices j))≤S.offsets i := by
    intro j _
    by_cases hj : j=i
    · subst j;exact (S.incident i).1.le
    by_cases hj' : j=finRotate n i
    · subst j;exact (S.incident i).2.le
    exact (S.nonincident i j hj hj').le
  have hstrict := S.nonincident i (finRotate n (finRotate n i))
    (centeredPolygonSupport_next_next_ne_self S.three_le i)
    (centeredPolygonSupport_next_ne_self S.three_le (finRotate n i))
  have hsum := Finset.sum_lt_sum hle ⟨finRotate n (finRotate n i),Finset.mem_univ _,hstrict⟩
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  rw [CyclicDiscPolygonSupportData.center,inner_smul_right,inner_sum,inv_mul_eq_div,div_lt_iff₀ hn]
  simpa only [mul_comm] using hsum

/-- Every center and bounded-body requirement is proved from the true cyclic support geometry. -/
def CyclicDiscPolygonSupportData.toCenteredData {n : ℕ} (S : CyclicDiscPolygonSupportData n) :
    CenteredDiscPolygonSupportData n where
  three_le := S.three_le
  vertices := S.vertices
  vertices_injective := S.vertices_injective
  normals := S.normals
  normal_norm := S.normal_norm
  offsets := S.offsets
  center := S.center
  center_strict := S.center_strict
  incident := S.incident
  nonincident := S.nonincident
  region_subset_closedBall := S.region_subset_closedBall

def CyclicDiscPolygonSupportData.toDiscPolygon {n : ℕ} (S : CyclicDiscPolygonSupportData n) : DiscPolygon n :=
  S.toCenteredData.toDiscPolygon

theorem CyclicDiscPolygonSupportData.toDiscPolygon_isConvex {n : ℕ} (S : CyclicDiscPolygonSupportData n) :
    S.toDiscPolygon.IsConvex := S.toCenteredData.toDiscPolygon_isConvex

theorem CyclicDiscPolygonSupportData.toDiscPolygon_angle {n : ℕ} (S : CyclicDiscPolygonSupportData n) (i : Fin n) :
    S.toDiscPolygon.angle i=(S.toCenteredData.cornerTriangle i).alpha := S.toCenteredData.angle_eq_cornerTriangle i

end
end LowDimensionalTopology.Geometry.Polygon
