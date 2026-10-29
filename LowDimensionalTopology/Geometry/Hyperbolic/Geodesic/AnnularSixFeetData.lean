module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AnnularCommonFeetDistinct
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AnnularOppositePerpendicularDisjoint
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AnnularOuterOppositePerpendicular
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeHyperbolicPencils
public import Mathlib.Data.Fin.VecNotation
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Set InnerProductGeometry
open scoped UpperHalfPlane
noncomputable section

/-- The original annular mirrors and actual six feet supply the fixed hexagon's geometric data. -/
theorem annular_six_feet_injective_and_nonadjacent_disjoint
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (hE1 : 1 < E)
    (hinner : 1 + r < x) (houter : x + r < E)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ) :
    let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
    let C2 := HalfPlaneLine.circle 0 E hE
    let C3 := HalfPlaneLine.circle x r hr
    C1.HDisjoint C2 → C1.HDisjoint C3 → C2.HDisjoint C3 →
    C1.OrthogonalAt K12 p12 → C2.OrthogonalAt K12 p21 →
    C2.OrthogonalAt K23 p23 → C3.OrthogonalAt K23 p32 →
    C3.OrthogonalAt K31 p31 → C1.OrthogonalAt K31 p13 →
    let vertex : Fin 6 → ℍ := ![p12, p21, p23, p32, p31, p13]
    let side : Fin 6 → HalfPlaneLine := ![K12, C2, K23, C3, K31, C1]
    Function.Injective vertex ∧
      ∀ i j : Fin 6, j ≠ i → j ≠ i + 1 → i ≠ j + 1 →
        Disjoint (side i).carrier (side j).carrier := by
  dsimp only
  intro hC12 hC13 hC23 h12 h21 h23 h32 h31 h13
  let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
  let C2 := HalfPlaneLine.circle 0 E hE
  let C3 := HalfPlaneLine.circle x r hr
  have hx : 0 < x := by linarith
  obtain ⟨n05, n12, n43⟩ :=
    annular_common_perpendicular_feet_ne E r x hE hr hE1 hx
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  have hpoint {L M : HalfPlaneLine} {p q : ℍ}
      (hd : Disjoint L.carrier M.carrier) (hp : p ∈ L.carrier) (hq : q ∈ M.carrier) :
      p ≠ q := by
    rintro rfl
    exact disjoint_left.mp hd hp hq
  have hseam {L K N : HalfPlaneLine} {p q : ℍ}
      (hp : L.OrthogonalAt K p) (hq : L.OrthogonalAt N q) (hpq : p ≠ q) : K ≠ N := by
    intro he
    subst N
    apply hpq
    apply dist_eq_zero.mp
    exact (L.pointDist_eq_dist_of_perpendicular K q p hq hp.2.1).symm.trans
      (Metric.infDist_zero_of_mem hp.1)
  have hsymm {L M : HalfPlaneLine} {p : ℍ} (h : L.OrthogonalAt M p) :
      M.Orthogonal L :=
    ⟨p, h.2.1, h.1, (real_inner_comm _ _).trans h.2.2⟩
  have d02 : Disjoint K12.carrier K23.carrier :=
    (hHyperbolicPencil_members_hDisjoint C2 (hsymm h21) (hsymm h23)
      (hseam h21 h23 n12)).2.2
  have d04 : Disjoint K12.carrier K31.carrier :=
    (hHyperbolicPencil_members_hDisjoint C1 (hsymm h12) (hsymm h13)
      (hseam h12 h13 n05)).2.2
  have d24 : Disjoint K23.carrier K31.carrier :=
    (hHyperbolicPencil_members_hDisjoint C3 (hsymm h32) (hsymm h31)
      (hseam h32 h31 n43.symm)).2.2
  have hK : K12 = HalfPlaneLine.vertical 0 :=
    concentric_commonOrthogonal_eq 1 E (by norm_num) hE (ne_of_lt hE1) K12
      ⟨p12, h12⟩ ⟨p21, h21⟩
  have d03 : Disjoint K12.carrier C3.carrier := by
    rw [hK]
    have hd : C3.HDisjoint (HalfPlaneLine.vertical 0) := by
      apply C3.hDisjoint_of_one_lt_abs_normalPairing (HalfPlaneLine.vertical 0)
      have hpair : C3.normalPairing (HalfPlaneLine.vertical 0) = -x / r := by
        simp only [C3, HalfPlaneLine.normalPairing, HalfPlaneLine.incenterNormal,
          HalfPlaneLine.incenterOffset,
          LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
        field_simp [hr.ne']
        ring
      rw [hpair, abs_div, abs_neg, abs_of_pos hx, abs_of_pos hr]
      exact (lt_div_iff₀ hr).mpr (by linarith)
    exact hd.2.2.symm
  have d14 : Disjoint C2.carrier K31.carrier :=
    (annular_outer_circle_hDisjoint_inner_common_perpendicular E r x hE hr hE1
      hinner houter K31 ⟨p13, h13⟩ ⟨p31, h31⟩).2.2
  have d25 : Disjoint K23.carrier C1.carrier :=
    (annular_inner_circle_hDisjoint_outer_common_perpendicular E r x hE hr hE1
      hinner houter K23 ⟨p23, h23⟩ ⟨p32, h32⟩).2.2.symm
  have d13 : Disjoint C2.carrier C3.carrier := hC23.2.2
  have d15 : Disjoint C2.carrier C1.carrier := hC12.2.2.symm
  have d35 : Disjoint C3.carrier C1.carrier := hC13.2.2.symm
  have n01 := hpoint hC12.2.2 h12.1 h21.1
  have n02 := hpoint hC12.2.2 h12.1 h23.1
  have n03 := hpoint hC13.2.2 h12.1 h32.1
  have n04 := hpoint hC13.2.2 h12.1 h31.1
  have n13 := hpoint hC23.2.2 h21.1 h32.1
  have n14 := hpoint hC23.2.2 h21.1 h31.1
  have n15 := hpoint hC12.2.2.symm h21.1 h13.1
  have n23 := hpoint hC23.2.2 h23.1 h32.1
  have n24 := hpoint hC23.2.2 h23.1 h31.1
  have n25 := hpoint hC12.2.2.symm h23.1 h13.1
  have n35 := hpoint hC13.2.2.symm h32.1 h13.1
  have n45 := hpoint hC13.2.2.symm h31.1 h13.1
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact False.elim (n01 hij)
    | exact False.elim (n01.symm hij)
    | exact False.elim (n02 hij)
    | exact False.elim (n02.symm hij)
    | exact False.elim (n03 hij)
    | exact False.elim (n03.symm hij)
    | exact False.elim (n04 hij)
    | exact False.elim (n04.symm hij)
    | exact False.elim (n05 hij)
    | exact False.elim (n05.symm hij)
    | exact False.elim (n12 hij)
    | exact False.elim (n12.symm hij)
    | exact False.elim (n13 hij)
    | exact False.elim (n13.symm hij)
    | exact False.elim (n14 hij)
    | exact False.elim (n14.symm hij)
    | exact False.elim (n15 hij)
    | exact False.elim (n15.symm hij)
    | exact False.elim (n23 hij)
    | exact False.elim (n23.symm hij)
    | exact False.elim (n24 hij)
    | exact False.elim (n24.symm hij)
    | exact False.elim (n25 hij)
    | exact False.elim (n25.symm hij)
    | exact False.elim (n35 hij)
    | exact False.elim (n35.symm hij)
    | exact False.elim (n43 hij)
    | exact False.elim (n43.symm hij)
    | exact False.elim (n45 hij)
    | exact False.elim (n45.symm hij)
  · intro i j hji hnext hprev
    fin_cases i <;> fin_cases j
    all_goals first
    | exact False.elim (hji (by decide))
    | exact False.elim (hnext (by decide))
    | exact False.elim (hprev (by decide))
    | exact d02
    | exact d02.symm
    | exact d03
    | exact d03.symm
    | exact d04
    | exact d04.symm
    | exact d13
    | exact d13.symm
    | exact d14
    | exact d14.symm
    | exact d15
    | exact d15.symm
    | exact d24
    | exact d24.symm
    | exact d25
    | exact d25.symm
    | exact d35
    | exact d35.symm

end
end LowDimensionalTopology.Geometry.Hyperbolic
