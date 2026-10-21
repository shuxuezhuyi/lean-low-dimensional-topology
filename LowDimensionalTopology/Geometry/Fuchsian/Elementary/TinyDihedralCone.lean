/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.TinyDihedralCycles
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A globally positive continuous height extends the actual tiny
family for its parameter-limit argument. -/
def tinyDihedralSafeHeight (t:ℝ) : ℝ:=Real.sqrt (max 1 (t-((t-1)/2)^2))

theorem tinyDihedralSafeHeight_pos (t:ℝ) : 0<tinyDihedralSafeHeight t := by
  apply Real.sqrt_pos.mpr
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

def tinyDihedralSafeVertex (t:ℝ) : ℍ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe ((t-1)/2) (tinyDihedralSafeHeight
    t) (tinyDihedralSafeHeight_pos t)

def tinyDihedralSafeCenter (t:ℝ) : ℍ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-((t-1)/2)) (tinyDihedralSafeHeight
    t) (tinyDihedralSafeHeight_pos t)

theorem tinyDihedral_safe_eq_actual (t:ℝ) (ht:1<t) (htu:t<2) :
    tinyDihedralSafeVertex t=tinyDihedralVertex t ht htu ∧
      tinyDihedralSafeCenter t=tinyDihedralCenter t ht htu := by
  have h:1≤t-((t-1)/2)^2:=by
    have hm:=mul_pos (sub_pos.mpr ht) (show 0<5-t by linarith only [htu])
    nlinarith only [hm]
  constructor <;> simp only [tinyDihedralSafeVertex,tinyDihedralSafeCenter,
    tinyDihedralSafeHeight,max_eq_right h,tinyDihedralVertex,tinyDihedralCenter]

theorem tinyDihedral_safe_continuous :
    Continuous tinyDihedralSafeVertex ∧ Continuous tinyDihedralSafeCenter := by
  have hh:Continuous tinyDihedralSafeHeight:=by unfold tinyDihedralSafeHeight;fun_prop
  have hx:Continuous (fun t:ℝ=>(t-1)/2):=by fun_prop
  constructor
  · apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun t:ℝ=>(⟨(t-1)/2,tinyDihedralSafeHeight t⟩:ℂ))
    exact Complex.equivRealProdCLM.symm.continuous.comp (hx.prodMk hh)
  · apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun t:ℝ=>(⟨-((t-1)/2),tinyDihedralSafeHeight t⟩:ℂ))
    exact Complex.equivRealProdCLM.symm.continuous.comp (hx.neg.prodMk hh)

theorem tinyDihedral_safe_one :
    tinyDihedralSafeVertex 1=UpperHalfPlane.I ∧ tinyDihedralSafeCenter 1=UpperHalfPlane.I := by
  constructor <;> apply UpperHalfPlane.ext <;> apply Complex.ext <;>
    norm_num [tinyDihedralSafeVertex,tinyDihedralSafeCenter,tinyDihedralSafeHeight,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]

/-- Both genuine original points approach i, so their actual nearest
three-point circle can be placed in any prescribed metric neighborhood. -/
theorem tinyDihedral_points_near_i (δ:ℝ) (hδ:0<δ) :
    ∃t:ℝ,∃ht:1<t,∃htu:t<2,
      dist (tinyDihedralCenter t ht htu) UpperHalfPlane.I<δ ∧
      dist (tinyDihedralVertex t ht htu) UpperHalfPlane.I<δ := by
  have hW:Tendsto tinyDihedralSafeCenter (𝓝 (1:ℝ)) (𝓝 UpperHalfPlane.I):=by
    simpa only [tinyDihedral_safe_one.2] using tinyDihedral_safe_continuous.2.continuousAt.tendsto (x:=(1:ℝ))
  have hV:Tendsto tinyDihedralSafeVertex (𝓝 (1:ℝ)) (𝓝 UpperHalfPlane.I):=by
    simpa only [tinyDihedral_safe_one.1] using tinyDihedral_safe_continuous.1.continuousAt.tendsto (x:=(1:ℝ))
  have he:∀ᶠt in 𝓝[>] (1:ℝ),1<t ∧ t<2 ∧
      dist (tinyDihedralSafeCenter t) UpperHalfPlane.I<δ ∧
      dist (tinyDihedralSafeVertex t) UpperHalfPlane.I<δ:=by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num:(1:ℝ)<2)),
      mem_nhdsWithin_of_mem_nhds (hW.eventually (Metric.ball_mem_nhds _ hδ)),
      mem_nhdsWithin_of_mem_nhds (hV.eventually (Metric.ball_mem_nhds _ hδ))] with t ht htu hwt hvt
    exact ⟨ht,htu,hwt,hvt⟩
  obtain ⟨t,ht,htu,hwt,hvt⟩:=he.exists
  refine ⟨t,ht,htu,?_,?_⟩
  · rwa [(tinyDihedral_safe_eq_actual t ht htu).2] at hwt
  · rwa [(tinyDihedral_safe_eq_actual t ht htu).1] at hvt

/-- The new parabolic-word cone is strictly outside the tiny nearest
circle, for an actually constructed sufficiently small parameter. -/
theorem tinyDihedral_radius_avoids_real_cone (ε:ℝ) (hε:0<ε) :
    ∃t:ℝ,∃ht:1<t,∃htu:t<2,
      dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)<ε ∧
      ∀u:ℍ,u.im≤|u.re|→
        dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)<
          dist (tinyDihedralCenter t ht htu) u := by
  let U:Set ℍ:={u| |u.re|<u.im}
  have ho:IsOpen U:=isOpen_lt UpperHalfPlane.continuous_re.abs UpperHalfPlane.continuous_im
  have hi:UpperHalfPlane.I∈U:=by change |(0:ℝ)|<1;norm_num
  obtain ⟨δ,hδ,hball⟩:=Metric.isOpen_iff.mp ho UpperHalfPlane.I hi
  let η:=min (ε/4) (δ/4)
  have hη:0<η:=lt_min (by positivity) (by positivity)
  have hηε:η≤ε/4:=min_le_left _ _
  have hηδ:η≤δ/4:=min_le_right _ _
  obtain ⟨t,ht,htu,hwt,hvt⟩:=tinyDihedral_points_near_i η hη
  have hr:dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)<2*η:=by
    have htri:=dist_triangle (tinyDihedralCenter t ht htu) UpperHalfPlane.I (tinyDihedralVertex t ht htu)
    rw [dist_comm UpperHalfPlane.I (tinyDihedralVertex t ht htu)] at htri
    linarith only [htri,hwt,hvt]
  refine ⟨t,ht,htu,by linarith only [hr,hηε,hε],?_⟩
  intro u hu
  have hfar:δ≤dist u UpperHalfPlane.I:=by
    by_contra hn
    have hm:u∈Metric.ball UpperHalfPlane.I δ:=not_le.mp hn
    have hh:=hball hm
    exact (not_lt.mpr hu) hh
  have htri:=dist_triangle u (tinyDihedralCenter t ht htu) UpperHalfPlane.I
  rw [dist_comm u (tinyDihedralCenter t ht htu)] at htri
  linarith only [hfar,htri,hr,hwt,hηδ,hδ]

end LowDimensionalTopology.Geometry.Fuchsian
