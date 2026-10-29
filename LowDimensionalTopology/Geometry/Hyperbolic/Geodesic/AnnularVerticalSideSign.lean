module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Transversals
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AnnularCommonFootSign
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open scoped UpperHalfPlane
noncomputable section

/-- All four nonincident feet have the negative native sign on the actual first side. -/
theorem annular_vertical_common_perpendicular_time_neg
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (hE1 : 1 < E) (hxr : r < x)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ) :
    let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
    let C2 := HalfPlaneLine.circle 0 E hE
    let C3 := HalfPlaneLine.circle x r hr
    C1.OrthogonalAt K12 p12 → C2.OrthogonalAt K12 p21 →
    C2.OrthogonalAt K23 p23 → C3.OrthogonalAt K23 p32 →
    C3.OrthogonalAt K31 p31 → C1.OrthogonalAt K31 p13 →
    K12.normalTimeAt p23 < 0 ∧ K12.normalTimeAt p32 < 0 ∧
      K12.normalTimeAt p31 < 0 ∧ K12.normalTimeAt p13 < 0 := by
  dsimp only
  intro h12 h21 h23 h32 h31 h13
  have hK : K12 = HalfPlaneLine.vertical 0 :=
    concentric_commonOrthogonal_eq 1 E (by norm_num) hE (ne_of_lt hE1) K12
      ⟨p12, h12⟩ ⟨p21, h21⟩
  have hsmall (p : ℍ) (hp : p ∈ (HalfPlaneLine.circle x r hr).carrier) :
      (HalfPlaneLine.vertical 0).normalTimeAt p < 0 := by
    change ‖(p : ℂ) - (x : ℂ)‖ = r at hp
    have hbound : |p.re - x| ≤ r := by
      simpa only [Complex.sub_re, Complex.ofReal_re, UpperHalfPlane.coe_re, hp]
        using Complex.abs_re_le_norm ((p : ℂ) - (x : ℂ))
    have hpRe : 0 < p.re := by linarith [(abs_le.mp hbound).1]
    rw [HalfPlaneLine.normalTimeAt_vertical, zero_sub]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hpRe) p.im_pos
  rw [hK]
  exact ⟨circle_common_perpendicular_foot_vertical_time_neg E r x hE hr hxr
      K23 p23 h23 ⟨p32, h32⟩,
    hsmall p32 h32.1, hsmall p31 h31.1,
    circle_common_perpendicular_foot_vertical_time_neg 1 r x (by norm_num) hr hxr
      K31 p13 h13 ⟨p31, h31⟩⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
