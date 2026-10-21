module
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Complex.Isometry

/-!
# Angular normal forms for pairs of planar directions.

Real-linear isometries normalize pairs of unit directions and transport their positive
cones to the cone bounded by directions at the given angle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology InnerProductGeometry
open scoped ComplexConjugate NNReal

namespace LowDimensionalTopology.Geometry.Euclidean

/-- An unordered proper pair of genuine unit rays has an actual rotational angular normal form. -/
theorem circle_pair_rotation_normal_form (u v : Circle) (θ : ℝ)
    (hθ : angle (u:ℂ) (v:ℂ)=θ) (hθπ : θ<Real.pi) :
    ∃L : ℂ ≃ₗᵢ[ℝ] ℂ,
      (L (u:ℂ)=1 ∧ L (v:ℂ)=(Circle.exp θ:ℂ)) ∨
      (L (v:ℂ)=1 ∧ L (u:ℂ)=(Circle.exp θ:ℂ)) := by
  obtain ⟨a,r,hr,hrπ,he⟩:=circle_exists_short_arc_endpoints u v (by rwa [hθ])
  have hrθ : 2*r=θ:=by
    rcases he with ⟨hu,hv⟩|⟨hv,hu⟩
    · rw [hu,hv,circle_exp_endpoint_angle a hr hrπ.le] at hθ
      exact hθ
    · rw [hu,hv,angle_comm,circle_exp_endpoint_angle a hr hrπ.le] at hθ
      exact hθ
  let L:=rotation (Circle.exp (-(a-r)))
  have hfirst : L (Circle.exp (a-r):ℂ)=1:=by
    change (Circle.exp (-(a-r))*Circle.exp (a-r):Circle)=((1:Circle):ℂ)
    rw [←Circle.exp_add,neg_add_cancel,Circle.exp_zero]
  have hsecond : L (Circle.exp (a+r):ℂ)=(Circle.exp θ:ℂ):=by
    change (Circle.exp (-(a-r))*Circle.exp (a+r):Circle)=(Circle.exp θ:ℂ)
    rw [←Circle.exp_add]
    congr 2
    linarith
  refine ⟨L,?_⟩
  rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact Or.inl ⟨hfirst,hsecond⟩
  · exact Or.inr ⟨hfirst,hsecond⟩

/-- Genuine positive cones are carried by the actual real-linear coordinate map. -/
theorem planar_isometry_positive_cone (L : ℂ ≃ₗᵢ[ℝ] ℂ) (u v z : ℂ) :
    z∈Submodule.span ℝ≥0 {u,v} ↔ L z∈Submodule.span ℝ≥0 {L u,L v} := by
  rw [Submodule.mem_span_pair,Submodule.mem_span_pair]
  constructor
  · rintro ⟨a,b,hz⟩
    refine ⟨a,b,?_⟩
    change (a:ℝ)•L u+(b:ℝ)•L v=L z
    rw [←map_smul,←map_smul,←map_add]
    exact congrArg L hz
  · rintro ⟨a,b,hz⟩
    refine ⟨a,b,L.injective ?_⟩
    change L ((a:ℝ)•u+(b:ℝ)•v)=L z
    rw [map_add,map_smul,map_smul]
    exact hz

/-- Every genuine proper two-ray cone has an actual orthogonal standard-angle chart. -/
theorem positive_cone_rotation_normal_form (u v : ℂ) (hu : u≠0) (hv : v≠0)
    (θ : ℝ) (hθ : angle u v=θ) (hθπ : θ<Real.pi) :
    ∃L : ℂ ≃ₗᵢ[ℝ] ℂ,∀z : ℂ,z∈Submodule.span ℝ≥0 {u,v} ↔
      L z∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp θ:ℂ)} := by
  let U:=Circle.exp (Complex.arg u)
  let V:=Circle.exp (Complex.arg v)
  have hU : ‖u‖•(U:ℂ)=u:=by
    simpa only [U,Complex.real_smul,Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I u
  have hV : ‖v‖•(V:ℂ)=v:=by
    simpa only [V,Complex.real_smul,Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I v
  have hangle : angle (U:ℂ) (V:ℂ)=θ:=by
    rw [←hU,←hV,angle_smul_left_of_pos _ _ (norm_pos_iff.mpr hu),
      angle_smul_right_of_pos _ _ (norm_pos_iff.mpr hv)] at hθ
    exact hθ
  obtain ⟨L,hL⟩:=circle_pair_rotation_normal_form U V θ hangle hθπ
  have hcone (z : ℂ) : z∈Submodule.span ℝ≥0 {u,v} ↔ z∈Submodule.span ℝ≥0 {(U:ℂ),(V:ℂ)}:=by
    rw [←hU,←hV]
    exact positiveCone_span_smul_mem_iff ‖u‖ ‖v‖ (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  refine ⟨L,?_⟩
  intro z
  apply (hcone z).trans
  have hm:=planar_isometry_positive_cone L (U:ℂ) (V:ℂ) z
  rcases hL with ⟨h1,h2⟩|⟨h1,h2⟩
  · rwa [h1,h2] at hm
  · rwa [h1,h2,Set.pair_comm (Circle.exp θ:ℂ) (1:ℂ)] at hm

end LowDimensionalTopology.Geometry.Euclidean
