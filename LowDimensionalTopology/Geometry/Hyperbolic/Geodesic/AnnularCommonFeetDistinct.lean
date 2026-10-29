module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Transversals
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open scoped UpperHalfPlane
noncomputable section

/-- The two common-perpendicular feet on each of the three concrete mirrors are distinct. -/
theorem annular_common_perpendicular_feet_ne
    (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) (hE1 : 1 < E) (hx : 0 < x)
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ) :
    let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
    let C2 := HalfPlaneLine.circle 0 E hE
    let C3 := HalfPlaneLine.circle x r hr
    C1.OrthogonalAt K12 p12 → C2.OrthogonalAt K12 p21 →
    C2.OrthogonalAt K23 p23 → C3.OrthogonalAt K23 p32 →
    C3.OrthogonalAt K31 p31 → C1.OrthogonalAt K31 p13 →
    p12 ≠ p13 ∧ p21 ≠ p23 ∧ p31 ≠ p32 := by
  dsimp only
  intro h12 h21 h23 h32 h31 h13
  let C1 := HalfPlaneLine.circle 0 1 (by norm_num)
  let C2 := HalfPlaneLine.circle 0 E hE
  let C3 := HalfPlaneLine.circle x r hr
  have hno (N : HalfPlaneLine) (h1 : C1.Orthogonal N)
      (h2 : C2.Orthogonal N) (h3 : C3.Orthogonal N) : False := by
    have hN : N = HalfPlaneLine.vertical 0 :=
      concentric_commonOrthogonal_eq 1 E (by norm_num) hE
        (ne_of_lt hE1) N h1 h2
    rw [hN, HalfPlaneLine.orthogonal_iff_coefficients] at h3
    change x = 0 at h3
    exact hx.ne' h3
  have hperp {L K N : HalfPlaneLine} {p q : ℍ}
      (hp : L.OrthogonalAt K p) (hq : L.OrthogonalAt N q) (he : p = q) :
      K = N := by
    subst q
    exact (L.existsUnique_perpendicular p).unique
      ⟨hp.2.1, ⟨p, hp⟩⟩ ⟨hq.2.1, ⟨p, hq⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hK := hperp h12 h13 he
    apply hno K12 ⟨p12, h12⟩ ⟨p21, h21⟩
    rw [hK]
    exact ⟨p31, h31⟩
  · intro he
    have hK := hperp h21 h23 he
    apply hno K12 ⟨p12, h12⟩ ⟨p21, h21⟩
    rw [hK]
    exact ⟨p32, h32⟩
  · intro he
    have hK := hperp h31 h32 he
    apply hno K31 ⟨p13, h13⟩ ?_ ⟨p31, h31⟩
    rw [hK]
    exact ⟨p23, h23⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
