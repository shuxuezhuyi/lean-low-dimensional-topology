/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HalfPlanes
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Actual horocyclic and hypercyclic regions
-/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- A genuine Euclidean half-plane cut inside the upper half-plane. -/
def hReCutLt (c : ℝ) : Set ℍ := {z | z.re < c}

theorem hReCutLt_isPreconnected (c : ℝ) : IsPreconnected (hReCutLt c) := by
  apply UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image.mp
  have he : ((↑) : ℍ → ℂ) '' hReCutLt c = {w : ℂ | 0 < w.im} ∩ {w : ℂ | w.re < c} := by
    ext z
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.im_pos,hu⟩
    · rintro ⟨hz,hr⟩
      exact ⟨UpperHalfPlane.mk z hz,hr,rfl⟩
  rw [he]
  exact ((convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear 0).inter
    (convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear c)).isPreconnected

theorem hReCutLt_eq_openHalfPlane (c : ℝ) (z : ℍ) (hz : z.re < c) :
    openHHalfPlane (.vertical c) z = hReCutLt c := by
  have hzN : z ∈ (HalfPlaneLine.vertical c).carrierᶜ := ne_of_lt hz
  apply subset_antisymm
  · intro u hu
    have hc := (isPreconnected_connectedComponentIn
      (F := (HalfPlaneLine.vertical c).carrierᶜ) (x := z)).image UpperHalfPlane.re
        UpperHalfPlane.continuous_re.continuousOn
    have hzI := mem_image_of_mem UpperHalfPlane.re (mem_connectedComponentIn hzN)
    have huI := mem_image_of_mem UpperHalfPlane.re hu
    by_contra hnot
    have hge : c ≤ u.re := not_lt.mp hnot
    obtain ⟨v,hv,hve⟩ := hc.ordConnected.out hzI huI ⟨hz.le,hge⟩
    exact connectedComponentIn_subset (HalfPlaneLine.vertical c).carrierᶜ z hv hve
  · apply (hReCutLt_isPreconnected c).subset_connectedComponentIn hz
    exact fun u hu => ne_of_lt hu

theorem hReCutLt_hConvex (c : ℝ) : HConvex (hReCutLt c) := by
  let z := metricProbe (c - 1) 1 (by norm_num)
  have hz : z.re < c := by change c - 1 < c; linarith
  rw [← hReCutLt_eq_openHalfPlane c z hz]
  exact openHHalfPlane_hConvex (.vertical c) z (ne_of_lt hz)

/-- Pulling a source convex set back by a genuine isometry preserves convexity. -/
theorem HConvex.isometry_preimage {S : Set ℍ} (hS : HConvex S) {f : ℍ → ℍ} (hf : Isometry f) :
    HConvex (f ⁻¹' S) := by
  intro z hz w hw u hu
  by_cases hzw : z = w
  · subst w
    rw [closedHSegment_self] at hu
    have hue : u = z := hu
    exact hue.symm ▸ hz
  · apply hS (f z) hz (f w) hw
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.image_closedHSegment hf hzw]
    exact mem_image_of_mem f hu

theorem intervalNormalizer_re_circle (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (intervalNormalizer (c-r) (c+r) (by linarith) • z).re =
      (r ^ 2 - ‖(z : ℂ) - (c : ℂ)‖ ^ 2) /
        Complex.normSq (UpperHalfPlane.denom (intervalNormalizer (c-r) (c+r) (by linarith)) z) := by
  change ((intervalNormalizer (c-r) (c+r) (by linarith) • z : ℍ) : ℂ).re = _
  rw [UpperHalfPlane.coe_smul_of_det_pos (by
    simpa using intervalNormalizer_pos (c-r) (c+r) (by linarith))]
  change (((1 : ℂ) * z + ((-(c-r) : ℝ) : ℂ)) / (((-1 : ℝ) : ℂ) * z + ((c+r : ℝ) : ℂ))).re =
    (r ^ 2 - ‖(z : ℂ) - (c : ℂ)‖ ^ 2) /
      Complex.normSq (((-1 : ℝ) : ℂ) * z + ((c+r : ℝ) : ℂ))
  have hn : ‖(z : ℂ) - (c : ℂ)‖ ^ 2 = (z.re-c) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      sub_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    ring
  rw [Complex.div_re,hn]
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,add_zero,sub_zero,
    UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

theorem intervalNormalizer_re_neg_iff_outside_circle (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (intervalNormalizer (c-r) (c+r) (by linarith) • z).re < 0 ↔ r < ‖(z : ℂ) - (c : ℂ)‖ := by
  rw [intervalNormalizer_re_circle c r hr z]
  have hd := UpperHalfPlane.normSq_denom_pos
    (intervalNormalizer (c-r) (c+r) (by linarith)) z.im_ne_zero
  rw [div_lt_iff₀ hd,zero_mul]
  constructor <;> intro h <;> nlinarith [norm_nonneg ((z : ℂ) - (c : ℂ))]

/-- The genuine exterior of a real-centred semicircle is hyperbolically convex. -/
theorem hConvex_outside_circle (c r : ℝ) (hr : 0 < r) :
    HConvex {z : ℍ | r < ‖(z : ℂ) - (c : ℂ)‖} := by
  let g := intervalNormalizer (c-r) (c+r) (by linarith)
  have he : {z : ℍ | r < ‖(z : ℂ) - (c : ℂ)‖} = (g • · : ℍ → ℍ) ⁻¹' hReCutLt 0 := by
    ext z
    exact (intervalNormalizer_re_neg_iff_outside_circle c r hr z).symm
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isometry_preimage (hReCutLt_hConvex
    0) (realGL_isometry g)

/-- The genuine semicircle exterior is the actual complementary half-plane component. -/
theorem openHHalfPlane_circle_outside (c r : ℝ) (hr : 0 < r) (z : ℍ)
    (hz : r < ‖(z : ℂ) - (c : ℂ)‖) :
    openHHalfPlane (.circle c r hr) z = {u : ℍ | r < ‖(u : ℂ) - (c : ℂ)‖} := by
  let L := HalfPlaneLine.circle c r hr
  let f : ℍ → ℝ := fun u => ‖(u : ℂ) - (c : ℂ)‖
  have hc : Continuous f := (UpperHalfPlane.continuous_coe.sub continuous_const).norm
  have hzN : z ∈ L.carrierᶜ := ne_of_gt hz
  apply subset_antisymm
  · intro u hu
    have hp := (isPreconnected_connectedComponentIn (F := L.carrierᶜ) (x := z)).image f hc.continuousOn
    have hzI := mem_image_of_mem f (mem_connectedComponentIn hzN)
    have huI := mem_image_of_mem f hu
    by_contra hnot
    have hle : f u ≤ r := not_lt.mp hnot
    obtain ⟨v,hv,he⟩ := hp.ordConnected.out huI hzI (show r ∈ Icc (f u) (f z) from ⟨hle,hz.le⟩)
    exact connectedComponentIn_subset L.carrierᶜ z hv he
  · apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isPreconnected (hConvex_outside_circle c r
    hr)).subset_connectedComponentIn hz
    exact fun u hu => ne_of_gt hu

/-- The normal horocyclic region based at the actual infinite ideal point. -/
def horizontalHorocyclicRegion (t : ℝ) : Set ℍ := {z | t < z.im}

/-- The source's actual intersection-of-half-planes representation. -/
theorem horizontalHorocyclicRegion_eq_iInter (t : ℝ) :
    horizontalHorocyclicRegion t = ⋂ c : ℝ,{z : ℍ | t < ‖(z : ℂ) - (c : ℂ)‖} := by
  ext z
  constructor
  · intro hz
    apply mem_iInter.mpr
    intro c
    have he : ‖(z : ℂ) - (c : ℂ)‖ ^ 2 = (z.re-c) ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simp
      ring
    have him : z.im ≤ ‖(z : ℂ) - (c : ℂ)‖ := by
      nlinarith [norm_nonneg ((z : ℂ) - (c : ℂ)),sq_nonneg (z.re-c),z.im_pos]
    exact lt_of_lt_of_le hz him
  · intro hz
    have hc := mem_iInter.mp hz z.re
    change t < ‖(z : ℂ) - (z.re : ℂ)‖ at hc
    have he : (z : ℂ) - (z.re : ℂ) = z.im * Complex.I := by
      apply Complex.ext <;> simp
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos z.im_pos,Complex.norm_I,mul_one] at hc
    exact hc

theorem horizontalHorocyclicRegion_hConvex (t : ℝ) (ht : 0 < t) :
    HConvex (horizontalHorocyclicRegion t) := by
  rw [horizontalHorocyclicRegion_eq_iInter]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter (fun c => hConvex_outside_circle c t ht)

/-- Rotation by an actual complex unit preserves the genuine native disc. -/
def discUnitRotation (u : ℂ) (hu : ‖u‖ = 1) (z : 𝔻) : 𝔻 :=
  Complex.UnitDisc.mk (u * z) (by simpa only [norm_mul,hu,one_mul] using z.norm_lt_one)

theorem discUnitRotation_coe (u : ℂ) (hu : ‖u‖ = 1) (z : 𝔻) :
    (discUnitRotation u hu z : ℂ) = u * z := rfl

theorem discUnitRotation_isometry (u : ℂ) (hu : ‖u‖ = 1) :
    letI := discHyperbolicMetric; Isometry (discUnitRotation u hu) := by
  let := discHyperbolicMetric
  apply Isometry.of_dist_eq
  intro z w
  change dist (discToHalfPlane (discUnitRotation u hu z)) (discToHalfPlane (discUnitRotation u hu w)) =
    dist (discToHalfPlane z) (discToHalfPlane w)
  apply Real.cosh_injOn dist_nonneg dist_nonneg
  rw [← discPathDist_eq_halfPlane,← discPathDist_eq_halfPlane]
  rw [disc_cosh_distance,disc_cosh_distance]
  simp only [discUnitRotation_coe,← mul_sub,norm_mul,hu,one_mul]

theorem DiscHConvex.isometry_preimage {S : Set 𝔻} (hS : DiscHConvex S) {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric; Isometry f → DiscHConvex (f ⁻¹' S) := by
  let := discHyperbolicMetric
  intro hf z hz w hw u hu
  by_cases hzw : z = w
  · subst w
    rw [closedDiscHSegment_self] at hu
    have hue : u = z := hu
    exact hue.symm ▸ hz
  · apply hS (f z) hz (f w) hw
    rw [← disc_isometry_image_closedHSegment hf hzw]
    exact mem_image_of_mem f hu

/-- Actual Euclidean discs internally tangent to the ideal unit circle. -/
def discHorocyclicRegion (ζ : ℂ) (r : ℝ) : Set 𝔻 :=
  {z | ‖(z : ℂ) - ((1-r : ℝ) : ℂ) * ζ‖ < r}

/-- The source definition retains an actual tangency point and a genuine proper tangent circle. -/
def IsDiscHorocyclicRegion (S : Set 𝔻) : Prop :=
  ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ r : ℝ, 0 < r ∧ r < 1 ∧ S = discHorocyclicRegion ζ r

/-- A horocycle is the actual model-topology boundary of its horocyclic region. -/
def discHorocycle (ζ : ℂ) (r : ℝ) : Set 𝔻 := frontier (discHorocyclicRegion ζ r)

theorem discHorocyclicRegion_one_iff_height (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (z : 𝔻) :
    z ∈ discHorocyclicRegion 1 r ↔ (1-r) / r < (discToHalfPlane z).im := by
  have hd : 0 < ‖1 - (z : ℂ)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (inverseCayley_denom_ne_zero z))
  have hN : ‖(z : ℂ) - ((1-r : ℝ) : ℂ)‖ ^ 2 = (z.re-(1-r)) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp
    ring
  have hD : ‖1 - (z : ℂ)‖ ^ 2 = (1-z.re) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp
    ring
  have hZ : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [Complex.UnitDisc.re,Complex.UnitDisc.im,pow_two]
  change ‖(z : ℂ) - ((1-r : ℝ) : ℂ) * 1‖ < r ↔ (1-r) / r < (inverseCayleyFormula z).im
  rw [mul_one,inverseCayley_im,lt_div_iff₀ hd,div_mul_eq_mul_div,div_lt_iff₀ hr,hD,hZ]
  constructor <;> intro h <;> nlinarith [norm_nonneg ((z : ℂ) - ((1-r : ℝ) : ℂ))]

theorem discHorocyclicRegion_one_eq_cayley_image (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    discHorocyclicRegion 1 r = halfPlaneToDisc '' horizontalHorocyclicRegion ((1-r)/r) := by
  ext z
  rw [discHorocyclicRegion_one_iff_height r hr hr1 z]
  constructor
  · intro hz
    exact ⟨discToHalfPlane z,hz,halfPlaneToDisc_discToHalfPlane z⟩
  · rintro ⟨w,hw,rfl⟩
    rw [discToHalfPlane_halfPlaneToDisc]
    exact hw

theorem discHorocyclicRegion_one_hConvex (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    DiscHConvex (discHorocyclicRegion 1 r) := by
  rw [discHorocyclicRegion_one_eq_cayley_image r hr hr1]
  exact (hConvex_iff_cayley_discHConvex _).mp
    (horizontalHorocyclicRegion_hConvex _ (div_pos (sub_pos.mpr hr1) hr))

theorem discHorocyclicRegion_eq_rotation_preimage (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ) :
    discHorocyclicRegion ζ r = (discUnitRotation (conj ζ) (by simpa only [Complex.norm_conj] using hζ)) ⁻¹'
      discHorocyclicRegion 1 r := by
  have hmul : conj ζ * ζ = 1 := by
    rw [mul_comm (conj ζ) ζ,Complex.mul_conj]
    have he : Complex.normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq,hζ,one_pow]
    exact_mod_cast he
  ext z
  change ‖(z : ℂ) - ((1-r : ℝ) : ℂ) * ζ‖ < r ↔
    ‖conj ζ * z - ((1-r : ℝ) : ℂ) * 1‖ < r
  have he : conj ζ * z - ((1-r : ℝ) : ℂ) * 1 = conj ζ * ((z : ℂ) - ((1-r : ℝ) : ℂ) * ζ) := by
    rw [mul_sub]
    linear_combination ((1-r : ℝ) : ℂ) * hmul
  rw [he,norm_mul,Complex.norm_conj,hζ,one_mul]

/-- Actual internally tangent Euclidean circle regions are hyperbolically convex. -/
theorem discHorocyclicRegion_hConvex (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    DiscHConvex (discHorocyclicRegion ζ r) := by
  rw [discHorocyclicRegion_eq_rotation_preimage ζ hζ r]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.isometry_preimage (discHorocyclicRegion_one_hConvex r hr hr1)
    (discUnitRotation_isometry _ _)

theorem IsDiscHorocyclicRegion.hConvex {S : Set 𝔻} (hS : IsDiscHorocyclicRegion S) : DiscHConvex S := by
  obtain ⟨ζ,hζ,r,hr,hr1,rfl⟩ := hS
  exact discHorocyclicRegion_hConvex ζ hζ r hr hr1

/-- The defining Euclidean circle has exactly the prescribed point of tangency with the
actual ideal unit circle. -/
theorem discHorocycle_euclidean_tangent (ζ : ℂ) (hζ : ‖ζ‖ = 1) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    {w : ℂ | ‖w - ((1-r : ℝ) : ℂ) * ζ‖ = r} ∩ {w : ℂ | ‖w‖ = 1} = {ζ} := by
  have hk : 0 < 1-r := sub_pos.mpr hr1
  have hc : ‖((1-r : ℝ) : ℂ) * ζ‖ = 1-r := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk,hζ,mul_one]
  ext w
  constructor
  · rintro ⟨hw,hW⟩
    have he := norm_sub_sq_real w (((1-r : ℝ) : ℂ) * ζ)
    rw [hw,hW,hc,← Complex.real_smul,inner_smul_right] at he
    have hi : inner ℝ w ζ = 1 := by nlinarith
    have hn := norm_sub_sq_real w ζ
    rw [hW,hζ,hi] at hn
    have hz : ‖w-ζ‖ = 0 := by nlinarith [norm_nonneg (w-ζ)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  · intro hw
    have hw' : w = ζ := hw
    subst w
    have he : ζ - ((1-r : ℝ) : ℂ) * ζ = (r : ℂ) * ζ := by push_cast; ring
    exact ⟨by
      change ‖ζ - ((1-r : ℝ) : ℂ) * ζ‖ = r
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,hζ,mul_one],hζ⟩

/-- The same native geometric horocyclic regions in the isometric H model. -/
def IsHHorocyclicRegion (S : Set ℍ) : Prop := IsDiscHorocyclicRegion (halfPlaneToDisc '' S)

def hHorocycle (S : Set ℍ) : Set ℍ := frontier S

theorem IsHHorocyclicRegion.hConvex {S : Set ℍ} (hS : IsHHorocyclicRegion S) : HConvex S :=
  (hConvex_iff_cayley_discHConvex
    S).mpr (_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsDiscHorocyclicRegion.hConvex hS)

/-- The original angle-defined normal hypercyclic region. -/
def hypercyclicStrip (θ : ℝ) : Set ℍ := {z | |Complex.arg (z : ℂ) - Real.pi / 2| < θ}

theorem hypercyclicStrip_angle_iff (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) (z : ℍ) :
    z ∈ hypercyclicStrip θ ↔ |z.re| < ‖(z : ℂ)‖ * Real.sin θ := by
  have harg : Complex.arg (z : ℂ) ∈ Icc (0 : ℝ) Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr z.im_pos.le,Complex.arg_le_pi _⟩
  have hleft : Real.pi / 2 - θ ∈ Icc (0 : ℝ) Real.pi := by constructor <;> linarith [Real.pi_pos]
  have hright : Real.pi / 2 + θ ∈ Icc (0 : ℝ) Real.pi := by constructor <;> linarith [Real.pi_pos]
  have hl := Real.strictAntiOn_cos.lt_iff_gt harg hleft
  have hr := Real.strictAntiOn_cos.lt_iff_gt hright harg
  rw [Real.cos_pi_div_two_sub] at hl
  rw [add_comm (Real.pi/2) θ,Real.cos_add_pi_div_two] at hr
  have he : |Complex.arg (z : ℂ) - Real.pi / 2| < θ ↔
      |Real.cos (Complex.arg (z : ℂ))| < Real.sin θ := by
    rw [abs_lt,abs_lt]
    constructor
    · intro h
      exact ⟨hr.mpr (by linarith),hl.mpr (by linarith)⟩
    · intro h
      have hL := hl.mp h.2
      have hR := hr.mp h.1
      constructor <;> linarith
  change |Complex.arg (z : ℂ) - Real.pi / 2| < θ ↔ _
  rw [he,Complex.cos_arg z.ne_zero,abs_div,abs_of_pos (norm_pos_iff.mpr z.ne_zero),
    div_lt_iff₀ (norm_pos_iff.mpr z.ne_zero)]
  rw [mul_comm,UpperHalfPlane.coe_re]

/-- The source's actual circle-half-plane intersection formula, with the original angle bound retained. -/
theorem hypercyclicStrip_eq_iInter (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    hypercyclicStrip θ = ⋂ c : ℝ,{z : ℍ | |c| * Real.cos θ < ‖(z : ℂ) - (c : ℂ)‖} := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθ'⟩
  ext z
  rw [hypercyclicStrip_angle_iff θ hθ hθ' z]
  have hZ : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,pow_two]
  have hN (c : ℝ) : ‖(z : ℂ) - (c : ℂ)‖ ^ 2 = (z.re-c) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp
    ring
  have hidentity (c : ℝ) :
      (‖(z : ℂ) - (c : ℂ)‖ ^ 2 - c ^ 2 * Real.cos θ ^ 2) * Real.sin θ ^ 2 =
        (c * Real.sin θ ^ 2 - z.re) ^ 2 + (‖(z : ℂ)‖ ^ 2 * Real.sin θ ^ 2 - z.re ^ 2) := by
    rw [hN,hZ,Real.cos_sq']
    ring
  constructor
  · intro h
    have hgap : 0 < ‖(z : ℂ)‖ ^ 2 * Real.sin θ ^ 2 - z.re ^ 2 := by
      have ha := sq_abs z.re
      nlinarith [abs_nonneg z.re,mul_nonneg (norm_nonneg (z : ℂ)) hs.le]
    apply mem_iInter.mpr
    intro c
    have hp : 0 < (‖(z : ℂ) - (c : ℂ)‖ ^ 2 - c ^ 2 * Real.cos θ ^ 2) * Real.sin θ ^ 2 := by
      rw [hidentity]
      nlinarith [sq_nonneg (c * Real.sin θ ^ 2-z.re)]
    have hd : 0 < ‖(z : ℂ) - (c : ℂ)‖ ^ 2 - c ^ 2 * Real.cos θ ^ 2 := by
      by_contra h
      have hnon := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (sq_nonneg (Real.sin θ))
      linarith
    have hr : 0 ≤ |c| * Real.cos θ := mul_nonneg (abs_nonneg c) hcos.le
    change |c| * Real.cos θ < ‖(z : ℂ) - (c : ℂ)‖
    apply (sq_lt_sq₀ hr (norm_nonneg _)).mp
    rw [mul_pow,sq_abs]
    linarith
  · intro h
    let c := z.re / Real.sin θ ^ 2
    have hc := mem_iInter.mp h c
    change |c| * Real.cos θ < ‖(z : ℂ) - (c : ℂ)‖ at hc
    have hr : 0 ≤ |c| * Real.cos θ := mul_nonneg (abs_nonneg c) hcos.le
    have hsq := (sq_lt_sq₀ hr (norm_nonneg ((z : ℂ) - (c : ℂ)))).mpr hc
    rw [mul_pow,sq_abs] at hsq
    have hd : 0 < ‖(z : ℂ) - (c : ℂ)‖ ^ 2 - c ^ 2 * Real.cos θ ^ 2 := by linarith
    have hp := mul_pos hd (sq_pos_of_pos hs)
    rw [hidentity] at hp
    have he : c * Real.sin θ ^ 2 - z.re = 0 := by
      dsimp [c]
      field_simp
      ring
    rw [he,zero_pow (by norm_num : 2 ≠ 0),zero_add] at hp
    have hAbs := sq_abs z.re
    nlinarith [abs_nonneg z.re,mul_nonneg (norm_nonneg (z : ℂ)) hs.le]

theorem hypercyclicStrip_hConvex (θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    HConvex (hypercyclicStrip θ) := by
  rw [hypercyclicStrip_eq_iInter θ hθ hθ']
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter
  intro c
  by_cases hc : c = 0
  · subst c
    have he : {z : ℍ | |(0 : ℝ)| * Real.cos θ < ‖(z : ℂ) - ((0 : ℝ) : ℂ)‖} = univ := by
      ext z
      change |(0 : ℝ)| * Real.cos θ < ‖(z : ℂ) - ((0 : ℝ) : ℂ)‖ ↔ True
      simp only [abs_zero,zero_mul,Complex.ofReal_zero,sub_zero,iff_true]
      exact norm_pos_iff.mpr z.ne_zero
    rw [he]
    exact fun _ _ _ _ _ _ => mem_univ _
  · exact hConvex_outside_circle c (|c| * Real.cos θ)
      (mul_pos (abs_pos.mpr hc) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθ'⟩))

/-- The source definition uses actual isometric congruence of its original angle region. -/
def IsHHypercyclicRegion (S : Set ℍ) : Prop :=
  ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧ ∃ f : ℍ → ℍ, Isometry f ∧ S = f '' hypercyclicStrip θ

def IsDiscHypercyclicRegion (S : Set 𝔻) : Prop :=
  letI := discHyperbolicMetric
  ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧ ∃ f : 𝔻 → 𝔻, Isometry f ∧
    S = f '' (halfPlaneToDisc '' hypercyclicStrip θ)

def hHypercycle (S : Set ℍ) : Set ℍ := frontier S
def discHypercycle (S : Set 𝔻) : Set 𝔻 := frontier S

theorem IsHHypercyclicRegion.hConvex {S : Set ℍ} (hS : IsHHypercyclicRegion S) : HConvex S := by
  obtain ⟨θ,hθ,hθ',f,hf,rfl⟩ := hS
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isometry_image (hypercyclicStrip_hConvex θ hθ hθ') hf

theorem IsDiscHypercyclicRegion.hConvex {S : Set 𝔻} (hS : IsDiscHypercyclicRegion S) : DiscHConvex S := by
  let := discHyperbolicMetric
  obtain ⟨θ,hθ,hθ',f,hf,rfl⟩ := hS
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.isometry_image ((hConvex_iff_cayley_discHConvex
    _).mp
    (hypercyclicStrip_hConvex θ hθ hθ')) hf

end
end LowDimensionalTopology.Geometry.Hyperbolic
