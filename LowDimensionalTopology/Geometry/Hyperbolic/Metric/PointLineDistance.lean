/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleAltitude
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Actual point-to-h-line distance and its unique perpendicular foot
-/

@[expose] public section
open Set
open scoped UpperHalfPlane Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- The genuine infimum over all points on the actual h-line. -/
def HalfPlaneLine.pointDist (L : HalfPlaneLine) (z : ℍ) : ℝ := Metric.infDist z L.carrier

theorem HalfPlaneLine.pointDist_eq_iInf (L : HalfPlaneLine) (z : ℍ) :
    L.pointDist z = ⨅ p : L.carrier, dist z p.val := Metric.infDist_eq_iInf

theorem HalfPlaneLine.pointDist_nonneg (L : HalfPlaneLine) (z : ℍ) : 0 ≤ L.pointDist z :=
  Metric.infDist_nonneg

theorem HalfPlaneLine.orthogonal_foot_dist_le (L M : HalfPlaneLine) (p z y : ℍ)
    (hp : L.OrthogonalAt M p) (hz : z ∈ M.carrier) (hy : y ∈ L.carrier) :
    dist z p ≤ dist z y := by
  have hc : Real.cosh (dist z p) ≤ Real.cosh (dist z y) := by
    rw [L.orthogonal_cosh_dist M p z y hp hz hy]
    have h1 := Real.one_le_cosh (dist p y)
    have h0 := (Real.cosh_pos (dist z p)).le
    nlinarith
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc

theorem HalfPlaneLine.orthogonal_foot_dist_eq_iff (L M : HalfPlaneLine) (p z y : ℍ)
    (hp : L.OrthogonalAt M p) (hz : z ∈ M.carrier) (hy : y ∈ L.carrier) :
    dist z y = dist z p ↔ y = p := by
  constructor
  · intro he
    have hc := L.orthogonal_cosh_dist M p z y hp hz hy
    rw [he] at hc
    have hcpos := Real.cosh_pos (dist z p)
    have hpy : Real.cosh (dist p y) = 1 := by nlinarith
    have hle : Real.cosh (dist p y) ≤ Real.cosh 0 := by rw [hpy,Real.cosh_zero]
    have hd : dist p y ≤ 0 := by
      simpa only [abs_of_nonneg dist_nonneg,abs_zero] using Real.cosh_le_cosh.mp hle
    exact (dist_eq_zero.mp (le_antisymm hd dist_nonneg)).symm
  · rintro rfl
    rfl

theorem HalfPlaneLine.pointDist_eq_dist_of_perpendicular (L M : HalfPlaneLine) (p z : ℍ)
    (hp : L.OrthogonalAt M p) (hz : z ∈ M.carrier) : L.pointDist z = dist z p := by
  apply le_antisymm (Metric.infDist_le_dist_of_mem hp.1)
  exact (Metric.le_infDist ⟨p,hp.1⟩).mpr (fun _ hy => L.orthogonal_foot_dist_le M p z _ hp hz hy)

theorem HalfPlaneLine.exists_unique_nearest_point (L : HalfPlaneLine) (z : ℍ) :
    ∃! p : ℍ, p ∈ L.carrier ∧ L.pointDist z = dist z p := by
  obtain ⟨M,⟨hz,⟨p,hp⟩⟩,_⟩ := L.existsUnique_perpendicular z
  have hd := L.pointDist_eq_dist_of_perpendicular M p z hp hz
  refine ⟨p,⟨hp.1,hd⟩,?_⟩
  intro y hy
  apply (L.orthogonal_foot_dist_eq_iff M p z y hp hz hy.1).mp
  exact hy.2.symm.trans hd

theorem HalfPlaneLine.exists_unique_orthogonal_foot (L : HalfPlaneLine) (z : ℍ) :
    ∃! p : ℍ, p ∈ L.carrier ∧ ∃ M : HalfPlaneLine, z ∈ M.carrier ∧ L.OrthogonalAt M p := by
  obtain ⟨M,⟨hz,⟨p,hp⟩⟩,_⟩ := L.existsUnique_perpendicular z
  refine ⟨p,⟨hp.1,M,hz,hp⟩,?_⟩
  rintro y ⟨hy,N,hzN,hyN⟩
  apply (L.orthogonal_foot_dist_eq_iff M p z y hp hz hy).mp
  exact (L.pointDist_eq_dist_of_perpendicular N y z hyN hzN).symm.trans
    (L.pointDist_eq_dist_of_perpendicular M p z hp hz)

def HalfPlaneLine.orthogonalFoot (L : HalfPlaneLine) (z : ℍ) : ℍ :=
  (L.exists_unique_nearest_point z).choose

theorem HalfPlaneLine.orthogonalFoot_mem (L : HalfPlaneLine) (z : ℍ) :
    L.orthogonalFoot z ∈ L.carrier := (L.exists_unique_nearest_point z).choose_spec.1.1

theorem HalfPlaneLine.pointDist_eq_orthogonalFoot (L : HalfPlaneLine) (z : ℍ) :
    L.pointDist z = dist z (L.orthogonalFoot z) := (L.exists_unique_nearest_point z).choose_spec.1.2

theorem HalfPlaneLine.orthogonalFoot_perpendicular (L : HalfPlaneLine) (z : ℍ) :
    ∃ M : HalfPlaneLine, z ∈ M.carrier ∧ L.OrthogonalAt M (L.orthogonalFoot z) := by
  obtain ⟨M,⟨hz,⟨p,hp⟩⟩,_⟩ := L.existsUnique_perpendicular z
  have he : L.orthogonalFoot z = p := (L.exists_unique_nearest_point z).choose_spec.2 _
    ⟨hp.1,L.pointDist_eq_dist_of_perpendicular M p z hp hz⟩ |>.symm
  exact ⟨M,hz,he.symm ▸ hp⟩


/-- The genuine infimum for the native disc's proved weighted path metric. -/
def DiscLine.pointDist (L : DiscLine) (z : 𝔻) : ℝ := by
  let := discHyperbolicMetric
  exact Metric.infDist z L.carrier

theorem DiscLine.pointDist_eq_halfPlane (L : DiscLine) (z : 𝔻) :
    L.pointDist z = L.toHalfPlane.pointDist (discToHalfPlane z) := by
  let := discHyperbolicMetric
  have he : discToHalfPlane '' L.carrier = L.toHalfPlane.carrier := by
    rw [L.carrier_eq_cayley_image_halfPlane,inverse_cayley_image_image]
  have h := Metric.infDist_image (x := z) (t := L.carrier) inverse_cayley_isometry
  rw [he] at h
  exact h.symm

theorem DiscLine.pointDist_eq_iInf (L : DiscLine) (z : 𝔻) :
    L.pointDist z = ⨅ p : L.carrier, discPathDist z p.val := by
  let := discHyperbolicMetric
  rw [DiscLine.pointDist,Metric.infDist_eq_iInf]
  congr 1
  funext p
  exact discHyperbolicMetric_distance _ _

theorem DiscLine.pointDist_nonneg (L : DiscLine) (z : 𝔻) : 0 ≤ L.pointDist z := by
  rw [L.pointDist_eq_halfPlane]
  exact L.toHalfPlane.pointDist_nonneg _

theorem DiscLine.orthogonalAt_iff_halfPlane (L M : DiscLine) (p : 𝔻) :
    L.OrthogonalAt M p ↔ L.toHalfPlane.OrthogonalAt M.toHalfPlane (discToHalfPlane p) := by
  constructor
  · intro hp
    have horth := (L.orthogonal_iff_halfPlane M).mp ((L.orthogonalAt_iff M p hp.1 hp.2.1).mp hp)
    have hcoeff := (L.toHalfPlane.orthogonal_iff_coefficients M.toHalfPlane).mp horth
    exact (L.toHalfPlane.orthogonalAt_iff_coefficients M.toHalfPlane (discToHalfPlane p)
      ((L.mem_carrier p).mp hp.1) ((M.mem_carrier p).mp hp.2.1)).mpr hcoeff
  · intro hp
    apply (L.orthogonalAt_iff M p ((L.mem_carrier p).mpr hp.1)
      ((M.mem_carrier p).mpr hp.2.1)).mpr
    exact (L.orthogonal_iff_halfPlane M).mpr ⟨discToHalfPlane p,hp⟩

theorem DiscLine.pointDist_eq_dist_of_perpendicular (L M : DiscLine) (p z : 𝔻)
    (hp : L.OrthogonalAt M p) (hz : z ∈ M.carrier) : L.pointDist z = discPathDist z p := by
  rw [L.pointDist_eq_halfPlane,discPathDist_eq_halfPlane]
  exact L.toHalfPlane.pointDist_eq_dist_of_perpendicular M.toHalfPlane _ _
    ((L.orthogonalAt_iff_halfPlane M p).mp hp) ((M.mem_carrier z).mp hz)

theorem DiscLine.orthogonal_foot_dist_eq_iff (L M : DiscLine) (p z y : 𝔻)
    (hp : L.OrthogonalAt M p) (hz : z ∈ M.carrier) (hy : y ∈ L.carrier) :
    discPathDist z y = discPathDist z p ↔ y = p := by
  rw [discPathDist_eq_halfPlane,discPathDist_eq_halfPlane]
  have he := L.toHalfPlane.orthogonal_foot_dist_eq_iff M.toHalfPlane
    (discToHalfPlane p) (discToHalfPlane z) (discToHalfPlane y)
    ((L.orthogonalAt_iff_halfPlane M p).mp hp) ((M.mem_carrier z).mp hz) ((L.mem_carrier y).mp hy)
  exact he.trans cayleyHomeomorph.symm.injective.eq_iff

theorem DiscLine.exists_unique_nearest_point (L : DiscLine) (z : 𝔻) :
    ∃! p : 𝔻, p ∈ L.carrier ∧ L.pointDist z = discPathDist z p := by
  obtain ⟨M,⟨hz,horth⟩,_⟩ := L.existsUnique_perpendicular z
  obtain ⟨p,hp⟩ := (L.orthogonal_iff_exists_orthogonalAt M).mp horth
  have hd := L.pointDist_eq_dist_of_perpendicular M p z hp hz
  refine ⟨p,⟨hp.1,hd⟩,?_⟩
  intro y hy
  apply (L.orthogonal_foot_dist_eq_iff M p z y hp hz hy.1).mp
  exact hy.2.symm.trans hd

theorem DiscLine.exists_unique_orthogonal_foot (L : DiscLine) (z : 𝔻) :
    ∃! p : 𝔻, p ∈ L.carrier ∧ ∃ M : DiscLine, z ∈ M.carrier ∧ L.OrthogonalAt M p := by
  obtain ⟨M,⟨hz,horth⟩,_⟩ := L.existsUnique_perpendicular z
  obtain ⟨p,hp⟩ := (L.orthogonal_iff_exists_orthogonalAt M).mp horth
  refine ⟨p,⟨hp.1,M,hz,hp⟩,?_⟩
  rintro y ⟨hy,N,hzN,hyN⟩
  apply (L.orthogonal_foot_dist_eq_iff M p z y hp hz hy).mp
  exact (L.pointDist_eq_dist_of_perpendicular N y z hyN hzN).symm.trans
    (L.pointDist_eq_dist_of_perpendicular M p z hp hz)

end
end LowDimensionalTopology.Geometry.Hyperbolic
