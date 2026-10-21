/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.Finite
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicOrthogonality
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.Geodesic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
@[expose] public section
noncomputable section
open Set
open scoped Topology UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The coordinate numerator identity for two real-centred circles meeting orthogonally. -/
theorem altitude_circle_circle_numerator_identity
    (c r d s x t v h p k : ℝ)
    (hy : (v - c) ^ 2 + h ^ 2 = r ^ 2)
    (hp : (p - c) ^ 2 + k ^ 2 = r ^ 2)
    (hz : (x - d) ^ 2 + t ^ 2 = s ^ 2)
    (hpM : (p - d) ^ 2 + k ^ 2 = s ^ 2)
    (hort : (c - d) ^ 2 = r ^ 2 + s ^ 2) :
    2 * k ^ 2 * ((x - v) ^ 2 + t ^ 2 + h ^ 2) =
      ((x - p) ^ 2 + t ^ 2 + k ^ 2) * ((p - v) ^ 2 + k ^ 2 + h ^ 2) := by
  have hzlin : (x - c) ^ 2 + t ^ 2 + r ^ 2 = 2 * (d - c) * (x - c) := by
    linear_combination hz - hort
  have hplin : (d - c) * (p - c) = r ^ 2 := by
    linear_combination (1 / 2 : ℝ) * hp + (1 / 2 : ℝ) * hort - (1 / 2 : ℝ) * hpM
  have hnzy : (x - v) ^ 2 + t ^ 2 + h ^ 2 = 2 * (x - c) * (d - v) := by
    linear_combination hzlin + hy
  have hnzp : (x - p) ^ 2 + t ^ 2 + k ^ 2 = 2 * (x - c) * (d - p) := by
    linear_combination hzlin + hp
  have hnpy : (p - v) ^ 2 + k ^ 2 + h ^ 2 = 2 * (p - c) * (d - v) := by
    linear_combination hp + hy - 2 * hplin
  have hk : k ^ 2 = (d - p) * (p - c) := by
    linear_combination hp - hplin
  rw [hnzy, hnzp, hnpy, hk]
  ring

/-- A genuine right-angle configuration satisfies the hyperbolic cosine identity by coordinates. -/
theorem HalfPlaneLine.orthogonal_cosh_dist (L M : HalfPlaneLine) (p z y : ℍ)
    (hp : L.OrthogonalAt M p) (hz : z ∈ M.carrier) (hy : y ∈ L.carrier) :
    Real.cosh (dist z y) = Real.cosh (dist z p) * Real.cosh (dist p y) := by
  have hcoeff := (L.orthogonalAt_iff_coefficients M p hp.1 hp.2.1).mp hp
  have hnum : 2 * p.im ^ 2 * ((z.re - y.re) ^ 2 + z.im ^ 2 + y.im ^ 2) =
      ((z.re - p.re) ^ 2 + z.im ^ 2 + p.im ^ 2) *
        ((p.re - y.re) ^ 2 + p.im ^ 2 + y.im ^ 2) := by
    cases L with
    | vertical x =>
      cases M with
      | vertical v => exact hcoeff.elim
      | circle c r hr =>
        change x = c at hcoeff
        rw [← hcoeff] at hp hz
        have hpL : p.re = x := hp.1
        have hyL : y.re = x := hy
        have hpM := norm_sub_real_eq_radius_sq hp.2.1
        have hzM := norm_sub_real_eq_radius_sq hz
        have he : (z.re - x) ^ 2 + z.im ^ 2 = p.im ^ 2 := by nlinarith [hpM, hzM]
        have hzy : (z.re - y.re) ^ 2 + z.im ^ 2 + y.im ^ 2 = p.im ^ 2 + y.im ^ 2 := by
          rw [hyL]
          linarith
        have hzp : (z.re - p.re) ^ 2 + z.im ^ 2 + p.im ^ 2 = 2 * p.im ^ 2 := by
          rw [hpL]
          linarith
        have hpy : (p.re - y.re) ^ 2 + p.im ^ 2 + y.im ^ 2 = p.im ^ 2 + y.im ^ 2 := by
          rw [hpL, hyL]
          ring
        rw [hzy, hzp, hpy]
    | circle c r hr =>
      cases M with
      | vertical x =>
        change c = x at hcoeff
        rw [← hcoeff] at hp hz
        have hpM : p.re = c := hp.2.1
        have hzM : z.re = c := hz
        have hpL := norm_sub_real_eq_radius_sq hp.1
        have hyL := norm_sub_real_eq_radius_sq hy
        have he : (y.re - c) ^ 2 + y.im ^ 2 = p.im ^ 2 := by nlinarith [hpL, hyL]
        have hzy : (z.re - y.re) ^ 2 + z.im ^ 2 + y.im ^ 2 = z.im ^ 2 + p.im ^ 2 := by
          rw [hzM]
          nlinarith [he]
        have hzp : (z.re - p.re) ^ 2 + z.im ^ 2 + p.im ^ 2 = z.im ^ 2 + p.im ^ 2 := by
          rw [hzM, hpM]
          ring
        have hpy : (p.re - y.re) ^ 2 + p.im ^ 2 + y.im ^ 2 = 2 * p.im ^ 2 := by
          rw [hpM]
          nlinarith [he]
        rw [hzy, hzp, hpy]
        ring
      | circle d s hs =>
        exact altitude_circle_circle_numerator_identity c r d s z.re z.im y.re y.im p.re p.im
          (norm_sub_real_eq_radius_sq hy) (norm_sub_real_eq_radius_sq hp.1)
          (norm_sub_real_eq_radius_sq hz) (norm_sub_real_eq_radius_sq hp.2.1) hcoeff
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist']
  field_simp
  linear_combination hnum

/-- An actual perpendicular foot never increases distance to any point of its base line. -/
theorem HalfPlaneLine.orthogonal_projection_dist_le (L M : HalfPlaneLine) (p z y : ℍ)
    (hp : L.OrthogonalAt M p) (hz : z ∈ M.carrier) (hy : y ∈ L.carrier) :
    dist p y ≤ dist z y := by
  have hc : Real.cosh (dist p y) ≤ Real.cosh (dist z y) := by
    rw [L.orthogonal_cosh_dist M p z y hp hz hy]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.one_le_cosh (dist z p))
      ((Real.one_le_cosh (dist p y)).trans' zero_le_one)
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hc

/-- A point of a real line lying within the endpoint distance of both endpoints is between them. -/
theorem altitude_real_bounded_endpoints (s t r : ℝ)
    (hs : dist s r ≤ dist s t) (ht : dist t r ≤ dist s t) :
    dist s r + dist r t = dist s t := by
  wlog hst : s ≤ t generalizing s t
  · have he := this t s (by simpa only [dist_comm] using ht)
      (by simpa only [dist_comm] using hs) (le_of_not_ge hst)
    simpa only [dist_comm, add_comm] using he
  have hdist : dist s t = t - s := by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]; ring
  rw [hdist, Real.dist_eq, abs_le] at hs ht
  apply (real_dist_triangle_eq_iff_mem_Icc hst).mpr
  constructor <;> linarith

/-- The same endpoint bound characterizes actual closed-segment membership on a complete h-line. -/
theorem HalfPlaneLine.mem_closedHSegment_of_endpoint_dist_le (L : HalfPlaneLine)
    {b c p : ℍ} (hbc : b ≠ c) (hb : b ∈ L.carrier) (hc : c ∈ L.carrier)
    (hp : p ∈ L.carrier) (hbp : dist b p ≤ dist b c) (hcp : dist c p ≤ dist b c) :
    p ∈ closedHSegment b c := by
  obtain ⟨γ, hγ, hrange⟩ := L.exists_isometric_param
  obtain ⟨s, hs⟩ := hrange.symm ▸ hb
  obtain ⟨t, ht⟩ := hrange.symm ▸ hc
  obtain ⟨r, hr⟩ := hrange.symm ▸ hp
  rw [← hs, ← ht, ← hr, hγ.dist_eq, hγ.dist_eq] at hbp hcp
  apply mem_closedHSegment_of_dist_triangle_eq hbc
  rw [← hs, ← ht, ← hr, hγ.dist_eq, hγ.dist_eq, hγ.dist_eq]
  exact altitude_real_bounded_endpoints s t r hbp hcp

/-- Every actual perpendicular foot to a longest side lies in the genuine closed side. -/
theorem HTriangle.altitude_foot_mem_sideA (T : HTriangle)
    (hlong : max (dist T.a T.b) (dist T.a T.c) ≤ dist T.b T.c)
    (M : HalfPlaneLine) (p : ℍ) (ha : T.a ∈ M.carrier)
    (hp : T.sideLineA.OrthogonalAt M p) : p ∈ T.sideA := by
  apply T.sideLineA.mem_closedHSegment_of_endpoint_dist_le T.b_ne_c
    T.rayBC.start_mem_support (T.rayBC.subset_support T.c_mem_rayBC) hp.1
  · rw [dist_comm T.b p]
    exact (T.sideLineA.orthogonal_projection_dist_le M p T.a T.b hp ha
      T.rayBC.start_mem_support).trans ((le_max_left _ _).trans hlong)
  · rw [dist_comm T.c p]
    exact (T.sideLineA.orthogonal_projection_dist_le M p T.a T.c hp ha
      (T.rayBC.subset_support T.c_mem_rayBC)).trans ((le_max_right _ _).trans hlong)

/-- In the actual finite half-plane model. -/
theorem HTriangle.exists_altitude_to_longest_side (T : HTriangle)
    (hlong : max (dist T.a T.b) (dist T.a T.c) ≤ dist T.b T.c) :
    ∃ M : HalfPlaneLine, T.a ∈ M.carrier ∧
      ∃ p ∈ T.sideA, T.sideLineA.OrthogonalAt M p := by
  obtain ⟨M, ⟨ha, hp⟩, _⟩ := T.sideLineA.existsUnique_perpendicular T.a
  obtain ⟨p, hp⟩ := hp
  exact ⟨M, ha, p, T.altitude_foot_mem_sideA hlong M p ha hp, hp⟩

/-- The native disc version for any actual side line and any actual perpendicular foot. -/
theorem DiscTriangle.altitude_foot_mem_sideA (T : DiscTriangle)
    (hlong : max (discPathDist T.a T.b) (discPathDist T.a T.c) ≤ discPathDist T.b T.c)
    (L M : DiscLine) (p : 𝔻) (hb : T.b ∈ L.carrier) (hc : T.c ∈ L.carrier)
    (ha : T.a ∈ M.carrier) (hp : L.OrthogonalAt M p) : p ∈ T.sideA := by
  have hlongH : max (dist T.toHalfPlane.a T.toHalfPlane.b)
      (dist T.toHalfPlane.a T.toHalfPlane.c) ≤ dist T.toHalfPlane.b T.toHalfPlane.c := by
    change max (dist (discToHalfPlane T.a) (discToHalfPlane T.b))
      (dist (discToHalfPlane T.a) (discToHalfPlane T.c)) ≤
        dist (discToHalfPlane T.b) (discToHalfPlane T.c)
    simpa only [discPathDist_eq_halfPlane] using hlong
  have hL : L.toHalfPlane = T.toHalfPlane.sideLineA :=
    L.toHalfPlane.eq_of_two_points _ T.toHalfPlane.b_ne_c
      ((L.mem_carrier T.b).mp hb) ((L.mem_carrier T.c).mp hc)
      T.toHalfPlane.rayBC.start_mem_support
      (T.toHalfPlane.rayBC.subset_support T.toHalfPlane.c_mem_rayBC)
  have horth : L.toHalfPlane.Orthogonal M.toHalfPlane :=
    (L.orthogonal_iff_halfPlane M).mp ((L.orthogonalAt_iff M p hp.1 hp.2.1).mp hp)
  have hcoeff := (L.toHalfPlane.orthogonal_iff_coefficients M.toHalfPlane).mp horth
  have hpH : L.toHalfPlane.OrthogonalAt M.toHalfPlane (discToHalfPlane p) :=
    (L.toHalfPlane.orthogonalAt_iff_coefficients M.toHalfPlane (discToHalfPlane p)
      ((L.mem_carrier p).mp hp.1) ((M.mem_carrier p).mp hp.2.1)).mpr hcoeff
  rw [hL] at hpH
  change discToHalfPlane p ∈ T.toHalfPlane.sideA
  exact T.toHalfPlane.altitude_foot_mem_sideA hlongH M.toHalfPlane (discToHalfPlane p)
    ((M.mem_carrier T.a).mp ha) hpH

/-- Using genuine native disc lines, normal orthogonality and weighted-path length. -/
theorem DiscTriangle.exists_altitude_to_longest_side (T : DiscTriangle)
    (hlong : max (discPathDist T.a T.b) (discPathDist T.a T.c) ≤ discPathDist T.b T.c) :
    ∃ L M : DiscLine, T.b ∈ L.carrier ∧ T.c ∈ L.carrier ∧ T.a ∈ M.carrier ∧
      ∃ p ∈ T.sideA, L.OrthogonalAt M p := by
  obtain ⟨L, ⟨hb, hc⟩, _⟩ := existsUnique_discLine_through T.b T.c T.b_ne_c
  obtain ⟨M, ⟨ha, horth⟩, _⟩ := L.existsUnique_perpendicular T.a
  obtain ⟨p, hp⟩ := (L.orthogonal_iff_exists_orthogonalAt M).mp horth
  exact ⟨L, M, hb, hc, ha, p, T.altitude_foot_mem_sideA hlong L M p hb hc ha hp, hp⟩

end LowDimensionalTopology.Geometry.Hyperbolic
