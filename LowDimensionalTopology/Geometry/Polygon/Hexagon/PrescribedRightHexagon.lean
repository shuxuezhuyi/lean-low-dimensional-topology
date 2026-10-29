module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.PrescribedAnnularMirrors
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AnnularSixFeetData
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineDistances
public import LowDimensionalTopology.Geometry.Polygon.Hexagon.SixFeetRightHexagon
@[expose] public section
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Hyperbolic
open scoped UpperHalfPlane
noncomputable section

/-- The prescribed half-boundary lengths are realized by the same actual annular six feet. -/
theorem exists_prescribed_annular_rightHexagon (a1 a2 a3 : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    ∃ Q : RightHexagon,
      Q.edgeLength 0 = a1 / 2 ∧ Q.edgeLength 2 = a2 / 2 ∧
      Q.edgeLength 4 = a3 / 2 ∧
      ∃ E r x : ℝ, ∃ hE : 0 < E, ∃ hr : 0 < r,
        1 < E ∧ 1 + r < x ∧ x + r < E ∧
        ∃ K12 K23 K31 : HalfPlaneLine, ∃ p12 p21 p23 p32 p31 p13 : ℍ,
          Q.vertex = ![p12, p21, p23, p32, p31, p13] ∧
          Q.side = ![K12, HalfPlaneLine.circle 0 E hE, K23,
            HalfPlaneLine.circle x r hr, K31, HalfPlaneLine.circle 0 1 (by norm_num)] := by
  obtain ⟨E, r, x, hE, hr, hE1, hinner, houter, hdata⟩ :=
    exists_prescribed_annular_three_mirrors (a1 / 2) (a3 / 2) (a2 / 2)
      (by positivity) (by positivity) (by positivity)
  dsimp only at hdata
  obtain ⟨hC12, hC13, hC23, hl12, hl13, hl23⟩ := hdata
  let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
  let C2 := HalfPlaneLine.circle 0 E hE
  let C3 := HalfPlaneLine.circle x r hr
  obtain ⟨K12, p12, p21, h12, h21, hd12, _⟩ :=
    C1.exists_commonOrthogonal_minimum C2 hC12
  obtain ⟨K23, p23, p32, h23, h32, hd23, _⟩ :=
    C2.exists_commonOrthogonal_minimum C3 hC23
  obtain ⟨K31, p13, p31, h13, h31, hd13, _⟩ :=
    C1.exists_commonOrthogonal_minimum C3 hC13
  obtain ⟨hinj, hdisj⟩ :=
    annular_six_feet_injective_and_nonadjacent_disjoint E r x hE hr hE1
      hinner houter K12 K23 K31 p12 p21 p23 p32 p31 p13
      hC12 hC13 hC23 h12 h21 h23 h32 h31 h13
  obtain ⟨Q, hvertex, hside⟩ :=
    exists_rightHexagon_of_six_feet C1 C2 C3 K12 K23 K31
      p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13 hinj hdisj
  have h0 : Q.edgeLength 0 = a1 / 2 := by
    simpa [RightHexagon.edgeLength, hvertex] using hd12.symm.trans hl12
  have h2 : Q.edgeLength 2 = a2 / 2 := by
    simpa [RightHexagon.edgeLength, hvertex] using hd23.symm.trans hl23
  have h4 : Q.edgeLength 4 = a3 / 2 := by
    simpa [RightHexagon.edgeLength, hvertex] using
      (dist_comm p31 p13).trans (hd13.symm.trans hl13)
  exact ⟨Q, h0, h2, h4, E, r, x, hE, hr, hE1, hinner, houter,
    K12, K23, K31, p12, p21, p23, p32, p31, p13, hvertex, hside⟩

/-- Every ordered positive triple occurs as the actual alternating half-boundary edge lengths. -/
theorem exists_prescribed_rightHexagon (a1 a2 a3 : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    ∃ Q : RightHexagon, Q.edgeLength 0 = a1 / 2 ∧
      Q.edgeLength 2 = a2 / 2 ∧ Q.edgeLength 4 = a3 / 2 := by
  obtain ⟨Q, h0, h2, h4, _⟩ :=
    exists_prescribed_annular_rightHexagon a1 a2 a3 ha1 ha2 ha3
  exact ⟨Q, h0, h2, h4⟩

end
end LowDimensionalTopology.Geometry.Polygon
