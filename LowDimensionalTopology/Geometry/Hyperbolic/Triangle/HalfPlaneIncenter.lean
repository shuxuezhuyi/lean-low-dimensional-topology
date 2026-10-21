module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.ClosedTriangleIncenter
@[expose] public section
open Set
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

def ClosedHTriangle.sideLineA (T : ClosedHTriangle) : HalfPlaneLine := T.toDiscTriangle.sideLineA.toHalfPlane
def ClosedHTriangle.sideLineB (T : ClosedHTriangle) : HalfPlaneLine := T.toDiscTriangle.sideLineB.toHalfPlane
def ClosedHTriangle.sideLineC (T : ClosedHTriangle) : HalfPlaneLine := T.toDiscTriangle.sideLineC.toHalfPlane

def ClosedHTriangle.cycle (T : ClosedHTriangle) : ClosedHTriangle where
  a := T.b
  b := T.c
  c := T.a
  noncollinear := by
    rintro ⟨L,hb,hc,ha⟩
    exact T.noncollinear ⟨L,ha,hb,hc⟩

theorem ClosedHTriangle.cycle_toDiscTriangle (T : ClosedHTriangle) :
    T.cycle.toDiscTriangle = T.toDiscTriangle.cycle := rfl

/-- The source bisector as a genuine half-plane geodesic through its actual finite or ideal vertex. -/
def IsClosedHTriangleInternalBisectorAtA (T : ClosedHTriangle) (L : HalfPlaneLine) : Prop :=
  T.a ∈ L.closedCarrier ∧ ∀ z ∈ T.interior,
    z ∈ L.carrier ↔ T.sideLineB.pointDist z = T.sideLineC.pointDist z

theorem IsClosedTriangleInternalBisectorAtA.toHalfPlane {T : ClosedHTriangle} {L : DiscLine}
    (hL : IsClosedTriangleInternalBisectorAtA T.toDiscTriangle L) :
    IsClosedHTriangleInternalBisectorAtA T L.toHalfPlane := by
  refine ⟨(L.closedCarrier_cayley_mem T.a).mp hL.1,?_⟩
  intro z hz
  have he := hL.2 (halfPlaneToDisc z) hz
  rw [L.mem_carrier,discToHalfPlane_halfPlaneToDisc,
    T.toDiscTriangle.sideLineB.pointDist_eq_halfPlane,T.toDiscTriangle.sideLineC.pointDist_eq_halfPlane,
    discToHalfPlane_halfPlaneToDisc] at he
  exact he

/-- The full finite-or-ideal concurrency theorem in the native half-plane model. -/
theorem ClosedHTriangle.exists_common_internal_angle_bisectors (T : ClosedHTriangle) :
    ∃ q ∈ T.interior, ∃ A B C : HalfPlaneLine,
      IsClosedHTriangleInternalBisectorAtA T A ∧ IsClosedHTriangleInternalBisectorAtA T.cycle B ∧
        IsClosedHTriangleInternalBisectorAtA T.cycle.cycle C ∧
        q ∈ A.carrier ∧ q ∈ B.carrier ∧ q ∈ C.carrier := by
  obtain ⟨q,hq,A,B,C,hA,hB,hC,hqA,hqB,hqC⟩ := T.toDiscTriangle.exists_common_internal_angle_bisectors
  have hqh : discToHalfPlane q ∈ T.interior := by
    change halfPlaneToDisc (discToHalfPlane q) ∈ T.toDiscTriangle.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hBh : IsClosedTriangleInternalBisectorAtA T.cycle.toDiscTriangle B := by
    rw [T.cycle_toDiscTriangle]
    exact hB
  have hCh : IsClosedTriangleInternalBisectorAtA T.cycle.cycle.toDiscTriangle C := by
    rw [T.cycle.cycle_toDiscTriangle,T.cycle_toDiscTriangle]
    exact hC
  exact ⟨discToHalfPlane q,hqh,A.toHalfPlane,B.toHalfPlane,C.toHalfPlane,hA.toHalfPlane,
    hBh.toHalfPlane,hCh.toHalfPlane,(A.mem_carrier q).mp hqA,(B.mem_carrier q).mp hqB,(C.mem_carrier q).mp hqC⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
