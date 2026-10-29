module

public import LowDimensionalTopology.Geometry.Polygon.Hexagon.HexagonNormals
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.DisjointLineNormalSigns

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set InnerProductGeometry
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Six cyclic right incidences with disjoint nonadjacent supports give a right hexagon. -/
def rightHexagonOfDisjointNonadjacent
    (vertex : Fin 6 → ℍ) (side : Fin 6 → HalfPlaneLine)
    (hinj : Function.Injective vertex)
    (hright : ∀ i : Fin 6,
      (side i).OrthogonalAt (side (i + 1)) (vertex (i + 1)))
    (hdisj : ∀ i j : Fin 6, j ≠ i → j ≠ i + 1 → i ≠ j + 1 →
      Disjoint (side i).carrier (side j).carrier) : RightHexagon := by
  have hnext : ∀ i : Fin 6, (i - 1) + 1 = i := by decide
  have hinc (i : Fin 6) : vertex i ∈ (side i).carrier := by
    simpa only [hnext] using (hright (i - 1)).2.1
  have htrans {a b c : ℝ} (hab : 0 < a * b) (hbc : 0 < b * c) :
      0 < a * c := by
    rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact mul_pos ha (pos_of_mul_pos_right hbc hb.le)
    · exact mul_pos_of_neg_of_neg ha (neg_of_mul_pos_right hbc hb.le)
  have hoff : ∀ i d : Fin 6, d = 2 ∨ d = 3 ∨ d = 4 →
      i + d ≠ i ∧ i + d ≠ i + 1 ∧ i ≠ i + d + 1 := by decide
  have hpositions : ∀ i j : Fin 6, j ≠ i → j ≠ i + 1 →
      j = i + 2 ∨ j = i + 3 ∨ j = i + 4 ∨ j = i + 5 := by decide
  refine ⟨vertex, hinj, side, hright, ?_⟩
  intro i j k hj hjnext hk hknext
  let f : Fin 6 → ℝ := fun m => (side i).normalTimeAt (vertex m)
  have hstep (d : Fin 6) (hd : d = 2 ∨ d = 3 ∨ d = 4) :
      0 < f (i + d) * f (i + d + 1) := by
    obtain ⟨h0, h1, h5⟩ := hoff i d hd
    exact (side i).normalTimeAt_mul_pos_of_disjoint (side (i + d))
      (hdisj i (i + d) h0 h1 h5) (hinc (i + d)) (hright (i + d)).1
  have h23 : 0 < f (i + 2) * f (i + 3) := by
    simpa only [add_assoc, show (2 : Fin 6) + 1 = 3 by decide] using hstep 2 (Or.inl rfl)
  have h34 : 0 < f (i + 3) * f (i + 4) := by
    simpa only [add_assoc, show (3 : Fin 6) + 1 = 4 by decide] using hstep 3 (Or.inr (Or.inl rfl))
  have h45 : 0 < f (i + 4) * f (i + 5) := by
    simpa only [add_assoc, show (4 : Fin 6) + 1 = 5 by decide] using hstep 4 (Or.inr (Or.inr rfl))
  have hself : 0 < f (i + 2) * f (i + 2) :=
    mul_self_pos.mpr (mul_ne_zero_iff.mp (ne_of_gt h23)).1
  have hanchor (m : Fin 6) (hm : m ≠ i) (hmnext : m ≠ i + 1) :
      0 < f (i + 2) * f m := by
    rcases hpositions i m hm hmnext with rfl | rfl | rfl | rfl
    · exact hself
    · exact h23
    · exact htrans h23 h34
    · exact htrans (htrans h23 h34) h45
  change 0 < f j * f k
  exact htrans (by simpa only [mul_comm] using hanchor j hj hjnext)
    (hanchor k hk hknext)

/-- The original six feet and six supports retain their literal cyclic order. -/
theorem exists_rightHexagon_of_six_feet
    (C1 C2 C3 K12 K23 K31 : HalfPlaneLine)
    (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : C1.OrthogonalAt K12 p12) (h21 : C2.OrthogonalAt K12 p21)
    (h23 : C2.OrthogonalAt K23 p23) (h32 : C3.OrthogonalAt K23 p32)
    (h31 : C3.OrthogonalAt K31 p31) (h13 : C1.OrthogonalAt K31 p13)
    (hinj : Function.Injective ![p12, p21, p23, p32, p31, p13])
    (hdisj : ∀ i j : Fin 6, j ≠ i → j ≠ i + 1 → i ≠ j + 1 →
      Disjoint (![K12, C2, K23, C3, K31, C1] i).carrier
        (![K12, C2, K23, C3, K31, C1] j).carrier) :
    ∃ Q : RightHexagon,
      Q.vertex = ![p12, p21, p23, p32, p31, p13] ∧
      Q.side = ![K12, C2, K23, C3, K31, C1] := by
  have hsymm {L M : HalfPlaneLine} {p : ℍ} (h : L.OrthogonalAt M p) :
      M.OrthogonalAt L p :=
    ⟨h.2.1, h.1, by rw [real_inner_comm]; exact h.2.2⟩
  have hright : ∀ i : Fin 6,
      (![K12, C2, K23, C3, K31, C1] i).OrthogonalAt
        (![K12, C2, K23, C3, K31, C1] (i + 1))
        (![p12, p21, p23, p32, p31, p13] (i + 1)) := by
    intro i
    fin_cases i
    · exact hsymm h21
    · exact h23
    · exact hsymm h32
    · exact h31
    · exact hsymm h13
    · exact h12
  exact ⟨rightHexagonOfDisjointNonadjacent _ _ hinj hright hdisj, rfl, rfl⟩

end LowDimensionalTopology.Geometry.Polygon
