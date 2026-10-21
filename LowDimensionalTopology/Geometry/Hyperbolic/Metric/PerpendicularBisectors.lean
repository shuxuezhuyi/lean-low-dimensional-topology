/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HypercycleDistance
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Genuine midpoints and perpendicular bisectors
-/
@[expose] public section
open Set
open scoped UpperHalfPlane MatrixGroups Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def HEquidistantLocus (a b : ℍ) : Set ℍ := {z | dist z a = dist z b}

def IsHMidpoint (a b w : ℍ) : Prop :=
  w ∈ closedHSegment a b ∧ dist a w = dist w b

theorem exists_hMidpoint {a b : ℍ} (hab : a ≠ b) : ∃ w, IsHMidpoint a b w := by
  obtain ⟨L,ha,hb⟩ := exists_halfPlaneLine_through a b hab
  obtain ⟨γ,hγ,hr⟩ := L.exists_isometric_param
  obtain ⟨s,rfl⟩ := hr.symm ▸ ha
  obtain ⟨t,rfl⟩ := hr.symm ▸ hb
  refine ⟨γ (midpoint ℝ s t),?_,?_⟩
  · apply mem_closedHSegment_of_dist_triangle_eq hab
    rw [hγ.dist_eq,hγ.dist_eq,hγ.dist_eq,dist_left_midpoint,dist_midpoint_right]
    norm_num
    ring
  · rw [hγ.dist_eq,hγ.dist_eq,dist_left_midpoint,dist_midpoint_right]

theorem IsHMidpoint.half_distance {a b w : ℍ} (h : IsHMidpoint a b w) :
    dist a w = dist a b / 2 ∧ dist w b = dist a b / 2 := by
  have ht := dist_triangle_eq_of_mem_closedHSegment h.1
  exact ⟨by linarith [h.2],by linarith [h.2]⟩

theorem vertical_equidistant_iff {a b : ℍ} (ha : a.re = 0) (hb : b.re = 0)
    (hi : a.im ≠ b.im) (z : ℍ) :
    dist z a = dist z b ↔ ‖(z : ℂ)‖ = Real.sqrt (a.im*b.im) := by
  have hc : Real.cosh (dist z a) = Real.cosh (dist z b) ↔ dist z a = dist z b :=
    ⟨Real.cosh_injOn (dist_nonneg) (dist_nonneg),congrArg Real.cosh⟩
  rw [← hc,UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',ha,hb]
  have hp : 0 < a.im*b.im := mul_pos a.im_pos b.im_pos
  have hsqrt := Real.sq_sqrt hp.le
  have hsqrtpos := Real.sqrt_pos.mpr hp
  have hn : ‖(z : ℂ)‖ ^ 2 = z.re^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    change z.re*z.re+z.im*z.im=z.re^2+z.im^2
    ring
  rw [div_eq_div_iff (by positivity : 2*z.im*a.im ≠ 0) (by positivity : 2*z.im*b.im ≠ 0)]
  rw [← sq_eq_sq₀ (norm_nonneg _) hsqrtpos.le,hn,hsqrt]
  have hzi : z.im ≠ 0 := z.im_ne_zero
  constructor
  · intro he
    have hh : (b.im-a.im)*(z.re^2+z.im^2-a.im*b.im)=0 := by
      apply (mul_left_cancel₀ (by positivity : (2*z.im) ≠ 0))
      nlinarith [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hi.symm))
  · intro he
    linear_combination 2*z.im*(b.im-a.im)*he

theorem exists_hEquidistantLine {a b : ℍ} (hab : a ≠ b) :
    ∃ N : HalfPlaneLine, N.carrier = HEquidistantLocus a b := by
  obtain ⟨u,v,g,_,_,_,_,_,_,ha,hb,hi⟩ := exists_ordered_ideal_normalizer a b hab
  let r := Real.sqrt ((g • a).im * (g • b).im)
  have hr : 0 < r := Real.sqrt_pos.mpr (mul_pos (g • a).im_pos (g • b).im_pos)
  let C := HalfPlaneLine.circle 0 r hr
  obtain ⟨N,hN⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine (realGL_isometry
    g⁻¹) C
  refine ⟨N,?_⟩
  ext (z : ℍ)
  rw [← hN]
  constructor
  · rintro ⟨w,hw,rfl⟩
    change dist (g⁻¹ • w) a = dist (g⁻¹ • w) b
    rw [← (realGL_isometry g).dist_eq (g⁻¹ • w) a,
      ← (realGL_isometry g).dist_eq (g⁻¹ • w) b,smul_inv_smul]
    apply (vertical_equidistant_iff ha hb (ne_of_lt hi) w).mpr
    change ‖(w : ℂ)-(0 : ℂ)‖=r at hw
    simpa only [sub_zero] using hw
  · intro hz
    refine ⟨g • z,?_,inv_smul_smul g z⟩
    change ‖((g • z : ℍ) : ℂ)-(0 : ℂ)‖=r
    rw [sub_zero]
    apply (vertical_equidistant_iff ha hb (ne_of_lt hi) (g • z)).mp
    change dist z a = dist z b at hz
    simpa only [realGL_distance] using hz


theorem HalfPlaneLine.closedHSegment_subset {a b : ℍ} (L : HalfPlaneLine)
    (hab : a ≠ b) (ha : a ∈ L.carrier) (hb : b ∈ L.carrier) :
    closedHSegment a b ⊆ L.carrier := by
  rintro w ⟨γ,hγ,s,t,_,hs,ht,r,_,rfl⟩
  have hr : range γ = L.carrier := isHLine_eq_of_two_points hγ.2 L.isHLine hab
    ⟨s,hs⟩ ⟨t,ht⟩ ha hb
  rw [← hr]
  exact mem_range_self r

theorem HalfPlaneLine.carrier_eq_equidistant_of_midpoint {a b w : ℍ}
    (L M : HalfPlaneLine) (hab : a ≠ b) (ha : a ∈ L.carrier) (hb : b ∈ L.carrier)
    (hw : IsHMidpoint a b w) (ho : L.OrthogonalAt M w) :
    M.carrier = HEquidistantLocus a b := by
  obtain ⟨N,hN⟩ := exists_hEquidistantLine hab
  have hsub : M.carrier ⊆ N.carrier := by
    intro z hz
    rw [hN]
    change dist z a = dist z b
    apply Real.cosh_injOn dist_nonneg dist_nonneg
    rw [L.orthogonal_cosh_dist M w z a ho hz ha,
      L.orthogonal_cosh_dist M w z b ho hz hb,dist_comm w a,hw.2]
  obtain ⟨u,v,hu,hv,huv⟩ := M.exists_two_points
  have he : M = N := M.eq_of_two_points N huv hu hv (hsub hu) (hsub hv)
  rw [he,hN]

/-- The geometric perpendicular bisector uses a genuine midpoint and genuine tangent orthogonality. -/
def IsHPerpendicularBisector (N : HalfPlaneLine) (a b : ℍ) : Prop :=
  ∃ (L : HalfPlaneLine) (w : ℍ), a ∈ L.carrier ∧ b ∈ L.carrier ∧
    IsHMidpoint a b w ∧ L.OrthogonalAt N w

theorem exists_hPerpendicularBisector {a b : ℍ} (hab : a ≠ b) :
    ∃ N : HalfPlaneLine, IsHPerpendicularBisector N a b := by
  obtain ⟨L,ha,hb⟩ := exists_halfPlaneLine_through a b hab
  obtain ⟨w,hw⟩ := exists_hMidpoint hab
  have hwL := L.closedHSegment_subset hab ha hb hw.1
  obtain ⟨N,⟨hwN,hcoeff⟩,_⟩ := L.existsUnique_perpendicular_coefficients w
  exact ⟨N,L,w,ha,hb,hw,(L.orthogonalAt_iff_coefficients N w hwL hwN).mpr hcoeff⟩

theorem IsHPerpendicularBisector.carrier_eq {N : HalfPlaneLine} {a b : ℍ}
    (h : IsHPerpendicularBisector N a b) (hab : a ≠ b) :
    N.carrier = HEquidistantLocus a b := by
  obtain ⟨L,w,ha,hb,hw,ho⟩ := h
  exact L.carrier_eq_equidistant_of_midpoint N hab ha hb hw ho

theorem existsUnique_hPerpendicularBisector {a b : ℍ} (hab : a ≠ b) :
    ∃! N : HalfPlaneLine, IsHPerpendicularBisector N a b := by
  obtain ⟨N,hN⟩ := exists_hPerpendicularBisector hab
  refine ⟨N,hN,?_⟩
  intro M hM
  obtain ⟨u,v,hu,hv,huv⟩ := M.exists_two_points
  have he : M.carrier = N.carrier := (hM.carrier_eq hab).trans (hN.carrier_eq hab).symm
  exact M.eq_of_two_points N huv hu hv (he ▸ hu) (he ▸ hv)

theorem hPerpendicularBisector_iff_carrier {N : HalfPlaneLine} {a b : ℍ} (hab : a ≠ b) :
    IsHPerpendicularBisector N a b ↔ N.carrier = HEquidistantLocus a b := by
  refine ⟨fun h => h.carrier_eq hab,?_⟩
  intro he
  obtain ⟨M,hM⟩ := exists_hPerpendicularBisector hab
  have hNM : N.carrier = M.carrier := he.trans (hM.carrier_eq hab).symm
  obtain ⟨u,v,hu,hv,huv⟩ := N.exists_two_points
  have hn : N=M := N.eq_of_two_points M huv hu hv (hNM ▸ hu) (hNM ▸ hv)
  exact hn ▸ hM


theorem IsHMidpoint.unique {a b w v : ℍ} (h : IsHMidpoint a b w)
    (hv : IsHMidpoint a b v) (hab : a ≠ b) : v = w := by
  obtain ⟨L,ha,hb⟩ := exists_halfPlaneLine_through a b hab
  have hwL := L.closedHSegment_subset hab ha hb h.1
  have hvL := L.closedHSegment_subset hab ha hb hv.1
  obtain ⟨N,⟨hwN,hcoeff⟩,_⟩ := L.existsUnique_perpendicular_coefficients w
  have ho : L.OrthogonalAt N w := (L.orthogonalAt_iff_coefficients N w hwL hwN).mpr hcoeff
  have he := L.carrier_eq_equidistant_of_midpoint N hab ha hb h ho
  have hvN : v ∈ N.carrier := by
    rw [he]
    change dist v a = dist v b
    rw [dist_comm v a]
    exact hv.2
  have hLN : L ≠ N := by
    intro hLN
    rw [← hLN] at ho
    have hp : 0 < inner ℝ (L.tangentAt w) (L.tangentAt w) :=
      real_inner_self_pos.mpr (L.tangentAt_ne_zero w)
    linarith [ho.2.2]
  exact L.inter_subsingleton hLN ⟨hvL,hvN⟩ ⟨hwL,hwN⟩

theorem existsUnique_hMidpoint {a b : ℍ} (hab : a ≠ b) : ∃! w, IsHMidpoint a b w := by
  obtain ⟨w,hw⟩ := exists_hMidpoint hab
  exact ⟨w,hw,fun v hv => hw.unique hv hab⟩

def DiscEquidistantLocus (a b : 𝔻) : Set 𝔻 := {z | discPathDist z a = discPathDist z b}

def IsDiscMidpoint (a b w : 𝔻) : Prop :=
  w ∈ closedDiscHSegment a b ∧ discPathDist a w = discPathDist w b

theorem isDiscMidpoint_iff_halfPlane (a b w : 𝔻) :
    IsDiscMidpoint a b w ↔ IsHMidpoint (discToHalfPlane a) (discToHalfPlane b) (discToHalfPlane w) := by
  simp only [IsDiscMidpoint,IsHMidpoint,closedDiscHSegment,mem_ofPred_eq,discPathDist_eq_halfPlane]

theorem isDiscMidpoint_iff_native (L : DiscLine) {a b w : 𝔻} (hab : a ≠ b)
    (ha : a ∈ L.carrier) (hb : b ∈ L.carrier) :
    IsDiscMidpoint a b w ↔ w ∈ nativeDiscClosedSegment L a b ∧
      discPathDist a w = discPathDist w b := by
  rw [nativeDiscClosedSegment_eq L hab ha hb]
  rfl

theorem existsUnique_discMidpoint {a b : 𝔻} (hab : a ≠ b) : ∃! w, IsDiscMidpoint a b w := by
  have hH : discToHalfPlane a ≠ discToHalfPlane b := fun he => hab (discToHalfPlane_injective he)
  obtain ⟨w,hw,huniq⟩ := existsUnique_hMidpoint hH
  refine ⟨halfPlaneToDisc w,?_,?_⟩
  · change IsDiscMidpoint a b (halfPlaneToDisc w)
    rw [isDiscMidpoint_iff_halfPlane,discToHalfPlane_halfPlaneToDisc]
    exact hw
  · intro v hv
    have he := huniq (discToHalfPlane v) ((isDiscMidpoint_iff_halfPlane a b v).mp hv)
    rw [← halfPlaneToDisc_discToHalfPlane v,he]

/-- Genuine orthogonality at a genuine native disc midpoint. -/
def IsDiscPerpendicularBisector (N : DiscLine) (a b : 𝔻) : Prop :=
  ∃ (L : DiscLine) (w : 𝔻), a ∈ L.carrier ∧ b ∈ L.carrier ∧
    IsDiscMidpoint a b w ∧ L.OrthogonalAt N w

theorem isDiscPerpendicularBisector_iff_halfPlane (N : DiscLine) (a b : 𝔻) :
    IsDiscPerpendicularBisector N a b ↔
      IsHPerpendicularBisector N.toHalfPlane (discToHalfPlane a) (discToHalfPlane b) := by
  constructor
  · rintro ⟨L,w,ha,hb,hw,ho⟩
    exact ⟨L.toHalfPlane,discToHalfPlane w,(L.mem_carrier a).mp ha,(L.mem_carrier b).mp hb,
      (isDiscMidpoint_iff_halfPlane a b w).mp hw,(L.orthogonalAt_iff_halfPlane N w).mp ho⟩
  · rintro ⟨L,w,ha,hb,hw,ho⟩
    refine ⟨L.toDiscLine,halfPlaneToDisc w,?_,?_,?_,?_⟩
    · rw [L.toDiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
      exact ha
    · rw [L.toDiscLine.mem_carrier,L.toDiscLine_toHalfPlane]
      exact hb
    · rw [isDiscMidpoint_iff_halfPlane,discToHalfPlane_halfPlaneToDisc]
      exact hw
    · rw [L.toDiscLine.orthogonalAt_iff_halfPlane,L.toDiscLine_toHalfPlane,
        discToHalfPlane_halfPlaneToDisc]
      exact ho

theorem IsDiscPerpendicularBisector.carrier_eq {N : DiscLine} {a b : 𝔻}
    (h : IsDiscPerpendicularBisector N a b) (hab : a ≠ b) :
    N.carrier = DiscEquidistantLocus a b := by
  have hH : discToHalfPlane a ≠ discToHalfPlane b := fun he => hab (discToHalfPlane_injective he)
  have he := ((isDiscPerpendicularBisector_iff_halfPlane N a b).mp h).carrier_eq hH
  ext z
  rw [N.mem_carrier,he]
  simp only [HEquidistantLocus,DiscEquidistantLocus,mem_ofPred_eq,discPathDist_eq_halfPlane]

theorem existsUnique_discPerpendicularBisector {a b : 𝔻} (hab : a ≠ b) :
    ∃! N : DiscLine, IsDiscPerpendicularBisector N a b := by
  have hH : discToHalfPlane a ≠ discToHalfPlane b := fun he => hab (discToHalfPlane_injective he)
  obtain ⟨N,hN,huniq⟩ := existsUnique_hPerpendicularBisector hH
  refine ⟨N.toDiscLine,?_,?_⟩
  · change IsDiscPerpendicularBisector N.toDiscLine a b
    rw [isDiscPerpendicularBisector_iff_halfPlane,N.toDiscLine_toHalfPlane]
    exact hN
  · intro M hM
    have he := huniq M.toHalfPlane ((isDiscPerpendicularBisector_iff_halfPlane M a b).mp hM)
    rw [← M.toHalfPlane_spec,he]

theorem discPerpendicularBisector_iff_carrier {N : DiscLine} {a b : 𝔻} (hab : a ≠ b) :
    IsDiscPerpendicularBisector N a b ↔ N.carrier = DiscEquidistantLocus a b := by
  refine ⟨fun h => h.carrier_eq hab,?_⟩
  intro he
  obtain ⟨M,hM,_⟩ := existsUnique_discPerpendicularBisector hab
  have hc : N.carrier = M.carrier := he.trans (hM.carrier_eq hab).symm
  have hHM : N.toHalfPlane.carrier = M.toHalfPlane.carrier := by
    apply cayleyHomeomorph.injective.image_injective
    change halfPlaneToDisc '' N.toHalfPlane.carrier = halfPlaneToDisc '' M.toHalfPlane.carrier
    rw [← N.carrier_eq_cayley_image_halfPlane,← M.carrier_eq_cayley_image_halfPlane]
    exact hc
  obtain ⟨u,v,hu,hv,huv⟩ := N.toHalfPlane.exists_two_points
  have hN : N.toHalfPlane = M.toHalfPlane := N.toHalfPlane.eq_of_two_points M.toHalfPlane
    huv hu hv (hHM ▸ hu) (hHM ▸ hv)
  have hn : N=M := by rw [← N.toHalfPlane_spec,← M.toHalfPlane_spec,hN]
  exact hn ▸ hM

end
end LowDimensionalTopology.Geometry.Hyperbolic
