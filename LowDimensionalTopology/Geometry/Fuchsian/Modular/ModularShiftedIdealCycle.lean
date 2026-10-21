/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularShiftedCycles
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicDirichletBoundary
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.IsometricCircle.BoundaryIsometricCircles
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ModularTriangleExample
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped UpperHalfPlane Topology OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem modular_shifted_height_lower (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z : ℍ) (hz : z∈modularClosedShiftedPolygon a) : 1/2≤z.im := by
  have hn : 1≤z.re*z.re+z.im*z.im:=hz.2.2.1
  have hn' := hz.2.2.2
  rw [modular_normSq_sub_one] at hn'
  change 1≤z.re*z.re+z.im*z.im+1-2*z.re at hn'
  have hx : z.re*z.re≤1/4 ∨ (z.re-1)*(z.re-1)≤1/4:=by
    by_cases h : z.re≤1/2
    · left
      have hp : (z.re+1/2)*(z.re-1/2)≤0:=mul_nonpos_of_nonneg_of_nonpos
        (by linarith [hz.1]) (by linarith)
      nlinarith
    · right
      have hp : (z.re-1+1/2)*(z.re-1-1/2)≤0:=mul_nonpos_of_nonneg_of_nonpos
        (by linarith) (by linarith [hz.2.1])
      nlinarith
  by_contra h
  have hy : z.im<1/2:=lt_of_not_ge h
  have hp : 0≤z.im*(1/2-z.im):=mul_nonneg z.im_pos.le (by linarith)
  rcases hx with hx|hx <;> nlinarith

theorem modular_shifted_finite_extended_closure_height (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0)
    (z : ℂ) (hz : (z:OnePoint ℂ)∈closure ((fun w : ℍ=>((w:ℂ):OnePoint ℂ)) ''
      modularShiftedPolygon a)) : 1/2≤z.im := by
  have hcl : z∈closure (((↑) : ℍ→ℂ) '' modularShiftedPolygon a):=by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
    simpa only [Set.mem_preimage,Set.image_image] using hz
  have hs : (((↑) : ℍ→ℂ) '' modularShiftedPolygon a)⊆{w : ℂ | 1/2≤w.im}:=by
    rintro w ⟨u,hu,rfl⟩
    exact modular_shifted_height_lower a ha₁ ha₂ u
      (modularShiftedPolygon_closure_subset a (subset_closure hu))
  exact closure_minimal hs (isClosed_le continuous_const Complex.continuous_im) hcl

theorem modular_shifted_infty_mem_closure (a : ℝ) :
    (∞:OnePoint ℂ)∈closure ((fun w : ℍ=>((w:ℂ):OnePoint ℂ)) '' modularShiftedPolygon a) := by
  apply mem_closure_of_tendsto (vertical_probe_tendsto_infty (a+1/2))
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_ge_atTop (2:ℝ))] with t ht
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (a+1/2) (Real.exp t) (Real.exp_pos t),?_,rfl⟩
  refine ⟨?_,?_,?_,?_⟩
  · change a<a+1/2
    linarith
  · change a+1/2<a+1
    linarith
  · change 1<(a+1/2)*(a+1/2)+Real.exp t*Real.exp t
    nlinarith [sq_nonneg (a+1/2)]
  · norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
    nlinarith [sq_nonneg (a+1/2-1)]

theorem modular_shifted_ideal_boundary (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    closure ((fun w : ℍ=>((w:ℂ):OnePoint ℂ)) '' modularShiftedPolygon a)∩_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis={∞} := by
  ext ξ
  constructor
  · rintro ⟨hξ,hreal⟩
    induction ξ using OnePoint.rec with
    | infty => exact Set.mem_singleton ∞
    | coe z =>
      have hh:=modular_shifted_finite_extended_closure_height a ha₁ ha₂ z hξ
      rw [_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis_coe] at hreal
      exact False.elim (by linarith)
  · rintro rfl
    exact ⟨modular_shifted_infty_mem_closure a,_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis_infty⟩

def modularExtendedPolygonCycle (D : Set ℍ) (ξ : OnePoint ℂ) : Set (OnePoint ℂ):=
  closure ((fun w : ℍ=>((w:ℂ):OnePoint ℂ)) '' D)∩
    MulAction.orbit _root_.LowDimensionalTopology.Geometry.Fuchsian.integralHalfPlaneMobiusHom.range ξ

theorem modular_sphere_infty_orbit_real :
    MulAction.orbit _root_.LowDimensionalTopology.Geometry.Fuchsian.integralHalfPlaneMobiusHom.range (∞:OnePoint ℂ)⊆_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis := by
  rintro ξ ⟨g,rfl⟩
  obtain ⟨A,hA⟩:=g.property
  change _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation (g.val.val ∞)=g.val.val ∞
  rw [←hA]
  change _root_.LowDimensionalTopology.Geometry.Mobius.complexConjugation ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) A)).val ∞)=_
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_commutes_complexConjugation _ ∞).symm

theorem modular_shifted_infty_cycle (a : ℝ) (ha₁ : -(1/2)<a) (ha₂ : a<0) :
    modularExtendedPolygonCycle (modularShiftedPolygon a) (∞:OnePoint ℂ)={∞} := by
  apply subset_antisymm
  · rintro ξ ⟨hξ,ho⟩
    rw [←modular_shifted_ideal_boundary a ha₁ ha₂]
    exact ⟨hξ,modular_sphere_infty_orbit_real ho⟩
  · rintro ξ rfl
    exact ⟨modular_shifted_infty_mem_closure a,MulAction.mem_orbit_self ∞⟩

end LowDimensionalTopology.Geometry.Fuchsian
