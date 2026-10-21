module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Fuchsian.Modular.ModularShiftedCycles
public import LowDimensionalTopology.Geometry.Polygon.Triangulation.PolygonMeshStraightAngles

/-! Genuine straight angular measure at the artificial cut in the shifted modular polygon. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
noncomputable section

/-- Cayley carries the actual closed left half-plane onto the native upper half-disc. -/
theorem modular_cayley_im_nonneg_iff (z : ℍ) :
    0 ≤ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ).im ↔ z.re ≤ 0 := by
  have hd : 0 < Complex.normSq ((z : ℂ) + Complex.I) :=
    Complex.normSq_pos.mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_denom_ne_zero z)
  change 0 ≤ (((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)).im ↔ _
  rw [Complex.div_im,← sub_div,le_div_iff₀ hd]
  simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.I_re,Complex.I_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
    sub_zero,add_zero,zero_mul]
  constructor <;> intro h <;> nlinarith

/-- A positive dilation of the genuine interval normalizer. -/
def modularRoundNormalizer (t : ℝ) (ht : 0 < t) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![t,t;-1,1]
    (by simp [Matrix.det_fin_two]; linarith)

theorem modularRoundNormalizer_coordinates (t : ℝ) (ht : 0 < t) (z : ℍ) :
    (modularRoundNormalizer t ht • z).re =
      t * (1 - Complex.normSq (z : ℂ)) / Complex.normSq (1 - (z : ℂ)) ∧
    (modularRoundNormalizer t ht • z).im =
      2 * t * z.im / Complex.normSq (1 - (z : ℂ)) := by
  have hp : 0 < (modularRoundNormalizer t ht).val.det := by
    simp [modularRoundNormalizer,Matrix.det_fin_two]
    linarith
  have he : ((modularRoundNormalizer t ht • z : ℍ) : ℂ) =
      ((t : ℂ) * z + t) / (1 - (z : ℂ)) := by
    rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hp)]
    simp [UpperHalfPlane.num,UpperHalfPlane.denom,modularRoundNormalizer]
    congr 1
    ring
  constructor
  · change (((modularRoundNormalizer t ht • z : ℍ) : ℂ)).re = _
    rw [he,Complex.div_re]
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.one_re,Complex.one_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
      Complex.normSq_apply,zero_mul,sub_zero,add_zero,zero_sub]
    ring
  · change (((modularRoundNormalizer t ht • z : ℍ) : ℂ)).im = _
    rw [he,Complex.div_im]
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.one_re,Complex.one_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
      zero_mul,sub_zero,add_zero,zero_sub]
    ring

theorem modularRoundNormalizer_exterior_iff (t : ℝ) (ht : 0 < t) (z : ℍ) :
    1 ≤ Complex.normSq (z : ℂ) ↔
      0 ≤ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (modularRoundNormalizer t ht • z) : ℂ).im := by
  have hn : (1 : ℂ) - (z : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.one_im,Complex.zero_im,UpperHalfPlane.coe_im] at hi
    linarith [z.im_pos]
  have hd : 0 < Complex.normSq (1 - (z : ℂ)) := Complex.normSq_pos.mpr hn
  rw [modular_cayley_im_nonneg_iff,(modularRoundNormalizer_coordinates t ht z).1,
    div_le_iff₀ hd]
  constructor <;> intro h <;> nlinarith

/-- A positive interval normalizer sends every actual unit-circle point to the standard basepoint. -/
theorem modularRoundNormalizer_exists_center (w : ℍ) (hw : Complex.normSq (w : ℂ) = 1) :
    ∃ t : ℝ, ∃ ht : 0 < t, modularRoundNormalizer t ht • w = UpperHalfPlane.I := by
  have hn : (1 : ℂ) - (w : ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.one_im,Complex.zero_im,UpperHalfPlane.coe_im] at hi
    linarith [w.im_pos]
  have hd : 0 < Complex.normSq (1 - (w : ℂ)) := Complex.normSq_pos.mpr hn
  let t := Complex.normSq (1 - (w : ℂ)) / (2 * w.im)
  have ht : 0 < t := div_pos hd (mul_pos (by norm_num) w.im_pos)
  refine ⟨t,ht,?_⟩
  apply UpperHalfPlane.coe_injective
  apply Complex.ext
  · change (modularRoundNormalizer t ht • w).re = UpperHalfPlane.I.re
    rw [(modularRoundNormalizer_coordinates t ht w).1,hw]
    norm_num
  · change (modularRoundNormalizer t ht • w).im = UpperHalfPlane.I.im
    rw [(modularRoundNormalizer_coordinates t ht w).2]
    dsimp [t]
    rw [UpperHalfPlane.I_im]
    field_simp [hd.ne',w.im_ne_zero]

/-- At the cut point the other three genuine defining constraints are strictly inactive. -/
theorem modularCutPoint_closed_germ (a : ℝ) (ha₁ : -(1/2) < a) (ha₂ : a < 0) :
    ∀ᶠ z in 𝓝 (modularCutPoint a ha₁ ha₂),
      z ∈ modularClosedShiftedPolygon a ↔ 1 ≤ Complex.normSq (z : ℂ) := by
  let w := modularCutPoint a ha₁ ha₂
  have hp := modularCutPoint_properties a ha₁ ha₂
  have hl : a < w.re := by rw [hp.1];linarith
  have hr : w.re < a + 1 := by rw [hp.1];linarith
  have hN : 1 < Complex.normSq ((w : ℂ) - 1) := by
    rw [modular_normSq_sub_one,hp.2.1,hp.1]
    linarith
  have hcont : Continuous (fun z : ℍ => Complex.normSq ((z : ℂ) - 1)) := by fun_prop
  filter_upwards [(isOpen_lt continuous_const UpperHalfPlane.continuous_re).mem_nhds hl,
    (isOpen_lt UpperHalfPlane.continuous_re continuous_const).mem_nhds hr,
    (isOpen_lt continuous_const hcont).mem_nhds hN] with z hzl hzr hzN
  change (a ≤ z.re ∧ z.re ≤ a + 1 ∧ 1 ≤ Complex.normSq (z : ℂ) ∧
    1 ≤ Complex.normSq ((z : ℂ) - 1)) ↔ _
  exact ⟨fun h => h.2.2.1,fun h => ⟨hzl.le,hzr.le,h,hzN.le⟩⟩

/-- A genuine convex region with a unit-geodesic exterior germ has a straight actual angle. -/
theorem modular_subtendedAngle_of_round_exterior_germ
    {S : Set ℍ}
    (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S)
    (w : ℍ) (hw : Complex.normSq (w : ℂ) = 1) (hwS : w ∈ S)
    (hG : ∀ᶠ z in 𝓝 w, z ∈ S ↔ 1 ≤ Complex.normSq (z : ℂ)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w) = Real.pi := by
  let modularCutDiscMetric : MetricSpace 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨t,ht,hcenter⟩ := modularRoundNormalizer_exists_center w hw
  let g := modularRoundNormalizer t ht
  let E : ℍ ≃ₜ 𝔻 := (Homeomorph.smul g).trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph
  let F : 𝔻 ≃ₜ 𝔻 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRealGLHomeomorph g
  have hF : Isometry F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRealGL_isometry g
  have hcomp : (fun z : ℍ => F (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) = (fun z => E z) := by
    funext z
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (g • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (g • z)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  have himage : F '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) = E '' S := by
    rw [image_image,hcomp]
  have hEw : E w = 0 := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (g • w) = 0
    rw [hcenter]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero ▸ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane 0
  have hInner (u : 𝔻) :
      0 ≤ inner ℝ (u : ℂ) Complex.I ↔ 0 ≤ (u : ℂ).im := by
    simp
  have hExterior : E '' {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} =
      {u : 𝔻 | 0 ≤ inner ℝ (u : ℂ) Complex.I} := by
    ext u
    constructor
    · rintro ⟨z,hz,rfl⟩
      apply (hInner _).mpr
      exact (modularRoundNormalizer_exterior_iff t ht z).mp hz
    · intro hu
      refine ⟨E.symm u,?_,E.apply_symm_apply u⟩
      apply (modularRoundNormalizer_exterior_iff t ht _).mpr
      change 0 ≤ (E (E.symm u) : ℂ).im
      rw [E.apply_symm_apply]
      exact (hInner _).mp hu
  have hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (E '' S) := by
    rw [←himage]
    exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hS).isometry_image hF
  have hzero : (0 : 𝔻) ∈ E '' S := ⟨w,hwS,hEw⟩
  have hgerm := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_homeomorph_germ E hG
  rw [hEw] at hgerm
  have hgerm' : ∀ᶠ u in 𝓝 (0 : 𝔻),
      u ∈ E '' S ↔ u ∈ {u : 𝔻 | 0 ≤ inner ℝ (u : ℂ) Complex.I} := by
    filter_upwards [hgerm] with u hu
    exact hu.trans (Set.ext_iff.mp hExterior u)
  have hang := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_eq_of_convex_germ hconv
    (_root_.LowDimensionalTopology.Geometry.Polygon.discHConvex_closed_halfPlane Complex.I) hzero (by simp) hgerm'
  have hiso := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F hF (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)
  have hFw : F (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w) = 0 := (congrFun hcomp w).trans hEw
  rw [himage,hFw] at hiso
  exact hiso.symm.trans (hang.trans (_root_.LowDimensionalTopology.Geometry.Polygon.discSubtendedAngle_closed_halfPlane Complex.I Complex.I_ne_zero))

/-- The artificial cut has its actual straight angular measure. -/
theorem modularCutPoint_subtendedAngle (a : ℝ) (ha₁ : -(1/2) < a) (ha₂ : a < 0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' modularClosedShiftedPolygon a)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (modularCutPoint a ha₁ ha₂)) = Real.pi := by
  have hconv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (modularClosedShiftedPolygon a) := by
    rw [←modularShiftedPolygon_closure]
    exact (modularShiftedPolygon_hConvex a).closure
  exact modular_subtendedAngle_of_round_exterior_germ hconv _
    (modularCutPoint_properties a ha₁ ha₂).2.1
    (modular_cut_cycle_points_closed a ha₁ ha₂).1
    (modularCutPoint_closed_germ a ha₁ ha₂)

end
end LowDimensionalTopology.Geometry.Fuchsian
