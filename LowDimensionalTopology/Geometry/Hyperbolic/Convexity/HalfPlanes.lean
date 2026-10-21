/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ModelCoordinates

/-!
# Actual half-planes and convex hyperbolic regions
-/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- An actual open half-plane is the connected component of the complement of a native disc line. -/
def openDiscHalfPlane (L : DiscLine) (z : 𝔻) : Set 𝔻 := connectedComponentIn L.carrierᶜ z

/-- Closed half-planes are the actual closures of the corresponding open components. -/
def closedDiscHalfPlane (L : DiscLine) (z : 𝔻) : Set 𝔻 := closure (openDiscHalfPlane L z)

/-- The same source connected-component convention in H. -/
def openHHalfPlane (L : HalfPlaneLine) (z : ℍ) : Set ℍ := connectedComponentIn L.carrierᶜ z

def closedHHalfPlane (L : HalfPlaneLine) (z : ℍ) : Set ℍ := closure (openHHalfPlane L z)

def discKleinCutLt (a : ℂ) (t : ℝ) : Set 𝔻 := {z | inner ℝ a (kleinCoordinate z) < t}
def discKleinCutGt (a : ℂ) (t : ℝ) : Set 𝔻 := {z | t < inner ℝ a (kleinCoordinate z)}

theorem discKleinCutLt_hConvex (a : ℂ) (t : ℝ) : DiscHConvex (discKleinCutLt a t) := by
  apply (discHConvex_iff_klein_convex _).mpr
  have he : kleinCoordinate '' discKleinCutLt a t =
      {w : ℂ | inner ℝ a w < t} ∩ Metric.ball (0 : ℂ) 1 := by
    change kleinCoordinate '' (kleinCoordinate ⁻¹' {w : ℂ | inner ℝ a w < t}) = _
    rw [image_preimage_eq_inter_range,range_kleinCoordinate]
  rw [he]
  exact (convex_halfSpace_lt (innerSL ℝ a).toLinearMap.isLinear t).inter (convex_ball (0 : ℂ) 1)

theorem discKleinCutGt_hConvex (a : ℂ) (t : ℝ) : DiscHConvex (discKleinCutGt a t) := by
  apply (discHConvex_iff_klein_convex _).mpr
  have he : kleinCoordinate '' discKleinCutGt a t =
      {w : ℂ | t < inner ℝ a w} ∩ Metric.ball (0 : ℂ) 1 := by
    change kleinCoordinate '' (kleinCoordinate ⁻¹' {w : ℂ | t < inner ℝ a w}) = _
    rw [image_preimage_eq_inter_range,range_kleinCoordinate]
  rw [he]
  exact (convex_halfSpace_gt (innerSL ℝ a).toLinearMap.isLinear t).inter (convex_ball (0 : ℂ) 1)

theorem DiscLine.exists_klein_linear_equation (L : DiscLine) :
    ∃ (a : ℂ) (t : ℝ), a ≠ 0 ∧ ∀ z : 𝔻,
      z ∈ L.carrier ↔ inner ℝ a (kleinCoordinate z) = t := by
  obtain ⟨a,t,ha,he⟩ := L.exists_klein_affine_equation
  refine ⟨a,t,ha,fun z => ?_⟩
  rw [real_inner_comm (kleinCoordinate z) a]
  exact he z

theorem connectedComponentIn_discLine_lt (L : DiscLine) (a : ℂ) (t : ℝ)
    (hL : ∀ z : 𝔻, z ∈ L.carrier ↔ inner ℝ a (kleinCoordinate z) = t)
    (z : 𝔻) (hz : inner ℝ a (kleinCoordinate z) < t) :
    openDiscHalfPlane L z = discKleinCutLt a t := by
  let f : 𝔻 → ℝ := fun u => inner ℝ a (kleinCoordinate u)
  have hc : Continuous f := (innerSL ℝ a).continuous.comp continuous_kleinCoordinate
  have hzN : z ∈ L.carrierᶜ := by
    intro hzL
    have he := (hL z).mp hzL
    linarith
  apply subset_antisymm
  · intro u hu
    have hpre := (isPreconnected_connectedComponentIn (F := L.carrierᶜ) (x := z)).image f hc.continuousOn
    have hzC : z ∈ connectedComponentIn L.carrierᶜ z := mem_connectedComponentIn hzN
    have hzI : f z ∈ f '' connectedComponentIn L.carrierᶜ z := mem_image_of_mem f hzC
    have huI : f u ∈ f '' connectedComponentIn L.carrierᶜ z := mem_image_of_mem f hu
    by_contra hnot
    have huge : t ≤ f u := not_lt.mp hnot
    obtain ⟨v,hv,he⟩ := hpre.ordConnected.out hzI huI (show t ∈ Icc (f z) (f u) from ⟨hz.le,huge⟩)
    have hvL : v ∈ L.carrier := (hL v).mpr he
    exact connectedComponentIn_subset L.carrierᶜ z hv hvL
  · apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.isPreconnected (discKleinCutLt_hConvex a
    t)).subset_connectedComponentIn hz
    intro u hu huL
    have he := (hL u).mp huL
    change inner ℝ a (kleinCoordinate u) < t at hu
    linarith

theorem connectedComponentIn_discLine_gt (L : DiscLine) (a : ℂ) (t : ℝ)
    (hL : ∀ z : 𝔻, z ∈ L.carrier ↔ inner ℝ a (kleinCoordinate z) = t)
    (z : 𝔻) (hz : t < inner ℝ a (kleinCoordinate z)) :
    openDiscHalfPlane L z = discKleinCutGt a t := by
  let f : 𝔻 → ℝ := fun u => inner ℝ a (kleinCoordinate u)
  have hc : Continuous f := (innerSL ℝ a).continuous.comp continuous_kleinCoordinate
  have hzN : z ∈ L.carrierᶜ := by
    intro hzL
    have he := (hL z).mp hzL
    linarith
  apply subset_antisymm
  · intro u hu
    have hpre := (isPreconnected_connectedComponentIn (F := L.carrierᶜ) (x := z)).image f hc.continuousOn
    have hzC : z ∈ connectedComponentIn L.carrierᶜ z := mem_connectedComponentIn hzN
    have hzI : f z ∈ f '' connectedComponentIn L.carrierᶜ z := mem_image_of_mem f hzC
    have huI : f u ∈ f '' connectedComponentIn L.carrierᶜ z := mem_image_of_mem f hu
    by_contra hnot
    have hule : f u ≤ t := not_lt.mp hnot
    obtain ⟨v,hv,he⟩ := hpre.ordConnected.out huI hzI (show t ∈ Icc (f u) (f z) from ⟨hule,hz.le⟩)
    have hvL : v ∈ L.carrier := (hL v).mpr he
    exact connectedComponentIn_subset L.carrierᶜ z hv hvL
  · apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.isPreconnected (discKleinCutGt_hConvex a
    t)).subset_connectedComponentIn hz
    intro u hu huL
    have he := (hL u).mp huL
    change t < inner ℝ a (kleinCoordinate u) at hu
    linarith

/-- The source open components are actual strict affine half-spaces after Klein. -/
theorem openDiscHalfPlane_eq_klein_cut (L : DiscLine) (z : 𝔻) (hz : z ∉ L.carrier) :
    ∃ (a : ℂ) (t : ℝ), a ≠ 0 ∧
      (openDiscHalfPlane L z = discKleinCutLt a t ∨ openDiscHalfPlane L z = discKleinCutGt a t) := by
  obtain ⟨a,t,ha,hL⟩ := L.exists_klein_linear_equation
  have hne : inner ℝ a (kleinCoordinate z) ≠ t := fun he => hz ((hL z).mpr he)
  refine ⟨a,t,ha,?_⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl (connectedComponentIn_discLine_lt L a t hL z hlt)
  · exact Or.inr (connectedComponentIn_discLine_gt L a t hL z hgt)

theorem openDiscHalfPlane_hConvex (L : DiscLine) (z : 𝔻) (hz : z ∉ L.carrier) :
    DiscHConvex (openDiscHalfPlane L z) := by
  obtain ⟨a,t,_,he | he⟩ := openDiscHalfPlane_eq_klein_cut L z hz
  · rw [he]
    exact discKleinCutLt_hConvex a t
  · rw [he]
    exact discKleinCutGt_hConvex a t

theorem closedDiscHalfPlane_hConvex (L : DiscLine) (z : 𝔻) (hz : z ∉ L.carrier) :
    DiscHConvex (closedDiscHalfPlane L
      z) := _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex.closure (openDiscHalfPlane_hConvex L z hz)

/-- Cayley carries actual complement components, rather than merely their half-space labels. -/
theorem cayley_image_openHHalfPlane (L : HalfPlaneLine) (z : ℍ) (hz : z ∉ L.carrier) :
    halfPlaneToDisc '' openHHalfPlane L z = openDiscHalfPlane L.toDiscLine (halfPlaneToDisc z) := by
  have he := cayleyHomeomorph.image_connectedComponentIn (show z ∈ L.carrierᶜ from hz)
  have hc : halfPlaneToDisc '' L.carrierᶜ = L.toDiscLine.carrierᶜ := by
    rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image]
    exact cayleyHomeomorph.toEquiv.image_compl L.carrier
  change halfPlaneToDisc '' openHHalfPlane L z = connectedComponentIn (halfPlaneToDisc '' L.carrierᶜ) (halfPlaneToDisc
    z) at he
  rwa [hc] at he

theorem openHHalfPlane_hConvex (L : HalfPlaneLine) (z : ℍ) (hz : z ∉ L.carrier) :
    HConvex (openHHalfPlane L z) := by
  apply (hConvex_iff_cayley_discHConvex _).mpr
  rw [cayley_image_openHHalfPlane L z hz]
  apply openDiscHalfPlane_hConvex
  intro h
  rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image] at h
  obtain ⟨w,hw,he⟩ := h
  exact hz (cayleyHomeomorph.injective he ▸ hw)

theorem closedHHalfPlane_hConvex (L : HalfPlaneLine) (z : ℍ) (hz : z ∉ L.carrier) :
    HConvex (closedHHalfPlane L
      z) := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.closure (openHHalfPlane_hConvex L z hz)

theorem mem_euclidean_segment_of_vertical_between {z w u : ℍ}
    (hr : z.re = w.re) (hi : z.im < w.im) (hur : u.re = z.re)
    (hzu : z.im ≤ u.im) (huw : u.im ≤ w.im) :
    (u : ℂ) ∈ segment ℝ (z : ℂ) (w : ℂ) := by
  rw [segment_eq_image']
  let θ := (u.im - z.im) / (w.im - z.im)
  have hden : 0 < w.im - z.im := sub_pos.mpr hi
  refine ⟨θ,⟨div_nonneg (sub_nonneg.mpr hzu) hden.le,
    (div_le_one hden).mpr (by linarith)⟩,?_⟩
  apply Complex.ext
  · simp only [Complex.add_re,Complex.smul_re,Complex.sub_re]
    change z.re + θ * (w.re - z.re) = u.re
    rw [← hr,sub_self,mul_zero,add_zero,hur]
  · simp only [Complex.add_im,Complex.smul_im,Complex.sub_im]
    change z.im + θ * (w.im - z.im) = u.im
    dsimp [θ]
    field_simp
    ring

/-- Genuine metric open discs in H are convex, proved using actual Euclidean metric balls
only after a genuine isometric normalization of the endpoint h-line. -/
theorem hConvex_metric_ball (c : ℍ) (r : ℝ) : HConvex (Metric.ball c r) := by
  intro z hz w hw u hu
  by_cases hzw : z = w
  · subst w
    rw [closedHSegment_self] at hu
    have hue : u = z := hu
    exact hue.symm ▸ hz
  obtain ⟨a,b,g,_,_,_,hg,_,_,hgz,hgw,hi⟩ := exists_ordered_ideal_normalizer z w hzw
  have htri : dist (g • z) (g • u) + dist (g • u) (g • w) = dist (g • z) (g • w) := by
    simpa only [realGL_distance] using dist_triangle_eq_of_mem_closedHSegment hu
  obtain ⟨hur,hzu,huw⟩ := (dist_triangle_eq_iff_vertical_between (hgz.trans hgw.symm) hi.le).mp htri
  have hseg := mem_euclidean_segment_of_vertical_between (hgz.trans hgw.symm) hi hur hzu huw
  have hzH : dist (g • z) (g • c) < r := by simpa only [Metric.mem_ball,Metric.mem_closedBall,realGL_distance] using hz
  have hwH : dist (g • w) (g • c) < r := by simpa only [Metric.mem_ball,Metric.mem_closedBall,realGL_distance] using hw
  have hzE := UpperHalfPlane.dist_lt_iff_dist_coe_center_lt.mp hzH
  have hwE := UpperHalfPlane.dist_lt_iff_dist_coe_center_lt.mp hwH
  have huE := (convex_ball ((g • c).center r : ℂ) ((g • c).im * Real.sinh r)).segment_subset hzE hwE hseg
  have huH := UpperHalfPlane.dist_lt_iff_dist_coe_center_lt.mpr huE
  simpa only [Metric.mem_ball,Metric.mem_closedBall,realGL_distance] using huH

theorem hConvex_metric_closedBall (c : ℍ) (r : ℝ) : HConvex (Metric.closedBall c r) := by
  intro z hz w hw u hu
  by_cases hzw : z = w
  · subst w
    rw [closedHSegment_self] at hu
    have hue : u = z := hu
    exact hue.symm ▸ hz
  obtain ⟨a,b,g,_,_,_,hg,_,_,hgz,hgw,hi⟩ := exists_ordered_ideal_normalizer z w hzw
  have htri : dist (g • z) (g • u) + dist (g • u) (g • w) = dist (g • z) (g • w) := by
    simpa only [realGL_distance] using dist_triangle_eq_of_mem_closedHSegment hu
  obtain ⟨hur,hzu,huw⟩ := (dist_triangle_eq_iff_vertical_between (hgz.trans hgw.symm) hi.le).mp htri
  have hseg := mem_euclidean_segment_of_vertical_between (hgz.trans hgw.symm) hi hur hzu huw
  have hzH : dist (g • z) (g • c) ≤ r := by simpa only [Metric.mem_ball,Metric.mem_closedBall,realGL_distance] using hz
  have hwH : dist (g • w) (g • c) ≤ r := by simpa only [Metric.mem_ball,Metric.mem_closedBall,realGL_distance] using hw
  have hzE := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mp hzH
  have hwE := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mp hwH
  have huE := (convex_closedBall ((g • c).center r : ℂ) ((g • c).im * Real.sinh r)).segment_subset hzE hwE hseg
  have huH := UpperHalfPlane.dist_le_iff_dist_coe_center_le.mpr huE
  simpa only [Metric.mem_ball,Metric.mem_closedBall,realGL_distance] using huH

theorem discHConvex_metric_ball (c : 𝔻) (r : ℝ) :
    letI := discHyperbolicMetric; DiscHConvex (Metric.ball c r) := by
  let := discHyperbolicMetric
  have he : Metric.ball c r = halfPlaneToDisc '' Metric.ball (discToHalfPlane c) r := by
    ext z
    constructor
    · intro hz
      exact ⟨discToHalfPlane z,hz,halfPlaneToDisc_discToHalfPlane z⟩
    · rintro ⟨w,hw,rfl⟩
      change dist (discToHalfPlane (halfPlaneToDisc w)) (discToHalfPlane c) < r
      rw [discToHalfPlane_halfPlaneToDisc]
      exact hw
  rw [he]
  exact (hConvex_iff_cayley_discHConvex _).mp (hConvex_metric_ball _ _)

theorem discHConvex_metric_closedBall (c : 𝔻) (r : ℝ) :
    letI := discHyperbolicMetric; DiscHConvex (Metric.closedBall c r) := by
  let := discHyperbolicMetric
  have he : Metric.closedBall c r = halfPlaneToDisc '' Metric.closedBall (discToHalfPlane c) r := by
    ext z
    constructor
    · intro hz
      exact ⟨discToHalfPlane z,hz,halfPlaneToDisc_discToHalfPlane z⟩
    · rintro ⟨w,hw,rfl⟩
      change dist (discToHalfPlane (halfPlaneToDisc w)) (discToHalfPlane c) ≤ r
      rw [discToHalfPlane_halfPlaneToDisc]
      exact hw
  rw [he]
  exact (hConvex_iff_cayley_discHConvex _).mp (hConvex_metric_closedBall _ _)

end
end LowDimensionalTopology.Geometry.Hyperbolic
