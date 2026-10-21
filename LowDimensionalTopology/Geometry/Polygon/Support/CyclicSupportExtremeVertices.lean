/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Polygon.Support.CyclicDiscPolygonSupports
public import Mathlib.Analysis.Convex.Extreme
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set InnerProductGeometry
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon

/-- Equality at a support level in a genuine strict convex combination forces equality at either end. -/
theorem complex_support_openSegment_left (n a b x:ℂ) (t:ℝ)
    (ha:inner ℝ n a≤t) (hb:inner ℝ n b≤t) (hx:inner ℝ n x=t)
    (h:x∈openSegment ℝ a b) : inner ℝ n a=t := by
  obtain ⟨α,β,hα,hβ,hαβ,hform⟩:=h
  have he:α*inner ℝ n a+β*inner ℝ n b=t:=by
    rw [←hx,←hform,inner_add_right,real_inner_smul_right,real_inner_smul_right]
  have hg:α*(t-inner ℝ n a)+β*(t-inner ℝ n b)=0:=by
    calc
      _=(α+β)*t-(α*inner ℝ n a+β*inner ℝ n b):=by ring
      _=0:=by rw [hαβ,one_mul,he,sub_self]
  have hzero:α*(t-inner ℝ n a)=0:=le_antisymm
    (by linarith [mul_nonneg hβ.le (sub_nonneg.mpr hb)])
    (mul_nonneg hα.le (sub_nonneg.mpr ha))
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hα.ne')).symm

/-- Every genuine cyclic-support vertex is an actual extreme point of its support body. This is derived from the two adjacent supports, rather than supplied as polygon data. -/
theorem CyclicDiscPolygonSupportData.vertex_mem_extreme {n:ℕ}
    (S:CyclicDiscPolygonSupportData n) (i:Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)∈S.toCenteredData.kleinRegion.extremePoints ℝ := by
  let v:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices i)
  let prev:=(finRotate n).symm i
  have hprev:finRotate n prev=i:=(finRotate n).apply_symm_apply i
  have hv:v∈S.toCenteredData.kleinRegion:=S.toCenteredData.vertex_mem_region i
  refine ⟨hv,?_⟩
  intro a ha b hb hopen
  by_contra hne
  have han:inner ℝ (S.normals i) a=S.offsets i:=
    complex_support_openSegment_left (S.normals i) a b v (S.offsets i) (ha i) (hb i)
      (S.incident i).1 hopen
  have hpn:inner ℝ (S.normals prev) v=S.offsets prev:=by
    simpa only [v,hprev] using (S.incident prev).2
  have hap:inner ℝ (S.normals prev) a=S.offsets prev:=
    complex_support_openSegment_left (S.normals prev) a b v (S.offsets prev) (ha prev) (hb prev) hpn hopen
  have hn: S.normals i≠0:=by
    intro he
    have hh:=S.normal_norm i
    rw [he,norm_zero] at hh
    exact zero_ne_one hh
  have hp: S.normals prev≠0:=by
    intro he
    have hh:=S.normal_norm prev
    rw [he,norm_zero] at hh
    exact zero_ne_one hh
  obtain ⟨k,_hk,hkp,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.complex_affine_normals_proportional (S.normals
    i) (S.normals prev)
    a v (S.offsets i) (S.offsets prev) hn hp hne han (S.incident i).1 hap hpn
  have hnq:inner ℝ (S.normals prev) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (S.vertices (finRotate n i)))=S.offsets prev:=by
    rw [hkp,real_inner_smul_left,(S.incident i).2]
    have he: k*S.offsets i=S.offsets prev:=by
      rw [←hpn,hkp,real_inner_smul_left]
      rw [(S.incident i).1]
    exact he
  have hlt:=S.nonincident prev (finRotate n i)
    (centeredPolygonSupport_prev_ne_next S.three_le i).symm
    (by rw [hprev];exact centeredPolygonSupport_next_ne_self S.three_le i)
  exact (ne_of_lt hlt) hnq
end LowDimensionalTopology.Geometry.Polygon
