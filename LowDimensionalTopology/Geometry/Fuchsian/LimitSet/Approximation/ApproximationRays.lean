module
public import LowDimensionalTopology.Geometry.Fuchsian.LimitSet.Approximation.PointsOfApproximation
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.DiscRays
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedGeodesicRays
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.MetricSpace.HausdorffDistance
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Asymptotics
open scoped UpperHalfPlane OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

theorem hRay_mem_iff_upward_of_endpoint_infty {z : ℍ} (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (hEnd : R.idealEndpoint = ∞) (w : ℍ) :
    w ∈ R.val ↔ w.re = z.re ∧ z.im ≤ w.im := by
  have hL := R.supportLine_of_idealEndpoint_infty hEnd
  have hsign : R.tangentSign = 1 := by
    have h := congrArg Complex.im (R.tangentVector_of_idealEndpoint_infty hEnd)
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentVector, hL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.tangentAt,
      Complex.smul_im, smul_eq_mul, Complex.I_im, mul_one] using h
  have hforward : R.longitudinal z < R.longitudinal R.directionPoint := by
    by_contra h
    have hs : R.tangentSign = -1 := by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.tangentSign, ite_eq_right h]
    linarith only [hs, hsign]
  constructor
  · intro hw
    have hline := R.subset_support hw
    have hm := (R.mem_iff_longitudinal hline).mp hw
    rw [ite_eq_left hforward] at hm
    refine ⟨by simpa only [hL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier, mem_ofPred_eq] using hline, ?_⟩
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.longitudinal, hL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.longitudinal,
      Complex.imCLM_apply, UpperHalfPlane.coe_im] using hm
  · rintro ⟨hre, him⟩
    have hline : w ∈ R.supportLine.carrier := by
      simpa only [hL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier, mem_ofPred_eq] using hre
    apply (R.mem_iff_longitudinal hline).mpr
    rw [ite_eq_left hforward]
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt.longitudinal, hL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.longitudinal,
      Complex.imCLM_apply, UpperHalfPlane.coe_im] using him

/-- The actual rays ending at infinity have a uniform finite one-sided distance bound. -/
theorem upward_hRays_uniform_distance
    {z v : ℍ}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt v)
    (hR : R.idealEndpoint = ∞) (hS : S.idealEndpoint = ∞) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ R.val, ∃ u ∈ S.val, dist w u ≤ M := by
  let k := 1+v.im/z.im
  have hk : 0 < k := by dsimp only [k]; positivity
  let C := (1+k^2)/(2*k)+(z.re-v.re)^2/(2*k*z.im^2)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC1 : 1 ≤ C := by
    have hbase : 1 ≤ (1+k^2)/(2*k) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith only [sq_nonneg (k-1)])
    exact hbase.trans (le_add_of_nonneg_right (by positivity))
  refine ⟨Real.arcosh C, Real.arcosh_nonneg hC1, ?_⟩
  intro w hw
  obtain ⟨hwr, hwy⟩ := (hRay_mem_iff_upward_of_endpoint_infty R hR w).mp hw
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe v.re (k*w.im) (mul_pos hk w.im_pos)
  have huy : v.im ≤ k*w.im := by
    have h := mul_le_mul_of_nonneg_left hwy hk.le
    have he : k*z.im = z.im+v.im := by dsimp only [k]; field_simp
    nlinarith only [h, he, z.im_pos]
  refine ⟨u, (hRay_mem_iff_upward_of_endpoint_infty S hS u).mpr ⟨rfl, huy⟩, ?_⟩
  have hcos : Real.cosh (dist w u) =
      (1+k^2)/(2*k)+(z.re-v.re)^2/(2*k*w.im^2) := by
    rw [UpperHalfPlane.cosh_dist', hwr]
    dsimp only [u, _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe, UpperHalfPlane.re, UpperHalfPlane.im]
    field_simp [ne_of_gt hk, w.im_ne_zero]
    ring
  have hsquares : z.im^2 ≤ w.im^2 := by nlinarith only [hwy, z.im_pos, w.im_pos]
  have hfrac : (z.re-v.re)^2/(2*k*w.im^2) ≤ (z.re-v.re)^2/(2*k*z.im^2) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left hsquares (by positivity))
  have hbound : Real.cosh (dist w u) ≤ C := by
    rw [hcos]
    exact add_le_add (le_refl _) hfrac
  have h := (Real.arcosh_le_arcosh (Real.cosh_pos _) hC).mpr hbound
  rwa [Real.arcosh_cosh dist_nonneg] at h

/-- Every two actual geodesic half-rays ending at the same ideal point are at bounded distance. -/
theorem same_endpoint_hRays_uniform_distance
    {z v : ℍ}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt v)
    (hEnd : R.idealEndpoint = S.idealEndpoint) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ R.val, ∃ u ∈ S.val, dist w u ≤ M := by
  obtain ⟨s, _, hR⟩ := R.exists_sl2_normalized_upward
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0 < g.val.det := by simp [g]
  have hS : (S.realGLMap g).idealEndpoint = ∞ := by
    rw [S.realGLMap_idealEndpoint g hg, ← hEnd, ← R.realGLMap_idealEndpoint g hg]
    exact hR
  obtain ⟨M, hM, hnear⟩ := upward_hRays_uniform_distance (R.realGLMap g) (S.realGLMap g) hR hS
  refine ⟨M, hM, ?_⟩
  intro w hw
  have hgw : g • w ∈ (R.realGLMap g).val := by
    rw [← R.realGLMap_carrier g]
    exact mem_image_of_mem (g • ·) hw
  obtain ⟨u', hu', hdist⟩ := hnear (g • w) hgw
  rw [← S.realGLMap_carrier g] at hu'
  obtain ⟨u, hu, rfl⟩ := hu'
  exact ⟨u, hu, by simpa only [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).dist_eq] using hdist⟩

/-- Bounded orbit distance and one compact transversal are equivalent for the
actual inverse images of any nonempty set in a proper metric space. -/
theorem isometric_orbit_infDist_iff_compact {X : Type*} [MetricSpace X] [ProperSpace X]
    (g : ℕ → X ≃ᵢ X) (S : Set X) (hS : S.Nonempty) (w : X) :
    (fun n => Metric.infDist (g n w) S) =O[atTop] (fun _ : ℕ => (1 : ℝ)) ↔
      ∃ K : Set X, IsCompact K ∧ ∀ n : ℕ, ((g n) ⁻¹' S ∩ K).Nonempty := by
  rw [isBigO_one_nat_atTop_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨Metric.closedBall w (C+1), isCompact_closedBall _ _, ?_⟩
    intro n
    have hdist : Metric.infDist (g n w) S < C+1 := by
      have h := hC n
      rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg] at h
      linarith only [h]
    obtain ⟨y, hy, hnear⟩ := (Metric.infDist_lt_iff hS).mp hdist
    refine ⟨(g n).symm y, ⟨?_, ?_⟩⟩
    · change g n ((g n).symm y) ∈ S
      simpa only [IsometryEquiv.apply_symm_apply] using hy
    · change dist ((g n).symm y) w ≤ C+1
      rw [← (g n).dist_eq, IsometryEquiv.apply_symm_apply]
      simpa only [dist_comm] using hnear.le
  · rintro ⟨K, hK, hmeet⟩
    obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall w
    refine ⟨C, ?_⟩
    intro n
    obtain ⟨x, hxS, hxK⟩ := hmeet n
    rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg]
    have hdist : Metric.infDist (g n w) S ≤ dist (g n w) (g n x) :=
      Metric.infDist_le_dist_of_mem hxS
    rw [(g n).dist_eq] at hdist
    exact hdist.trans (by simpa only [Metric.mem_closedBall, dist_comm] using hC hxK)

theorem disc_hyperbolic_properSpace :
    let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric; ProperSpace 𝔻 := by
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_isometry.antilipschitzWith.properSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_isometry.continuous
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.surjective

theorem same_endpoint_discRays_uniform_distance
    {z v : 𝔻}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z)
    (S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v)
    (hEnd : R.idealEndpoint = S.idealEndpoint) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ R.val, ∃ u ∈ S.val, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist w u ≤ M := by
  have hH : R.toHalfPlane.idealEndpoint = S.toHalfPlane.idealEndpoint := by
    rw [R.toHalfPlane_idealEndpoint, S.toHalfPlane_idealEndpoint, hEnd]
  obtain ⟨M, hM, hnear⟩ := same_endpoint_hRays_uniform_distance R.toHalfPlane S.toHalfPlane hH
  refine ⟨M, hM, ?_⟩
  intro w hw
  obtain ⟨uH, huH, hd⟩ := hnear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) ⟨w, hw, rfl⟩
  obtain ⟨u, hu, rfl⟩ := huH
  exact ⟨u, hu, by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]⟩

theorem disc_orbit_ray_infDist_iff_compact
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (g : ℕ → H)
    {v : 𝔻}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v)
    (w : 𝔻) :
    (let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric;
      (fun n => Metric.infDist (P.discAction (g n) w) R.val) =O[atTop] (fun _ : ℕ => (1 : ℝ))) ↔
      ∃ K : Set 𝔻, IsCompact K ∧ ∀ n : ℕ, ((P.discAction (g n)) ⁻¹' R.val ∩ K).Nonempty := by
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have : ProperSpace 𝔻 := disc_hyperbolic_properSpace
  let E : ℕ → 𝔻 ≃ᵢ 𝔻 := fun n =>
    ⟨(P.discAction (g n)).toEquiv, P.discAction_isometry (g n)⟩
  exact isometric_orbit_infDist_iff_compact E R.val ⟨v, R.start_mem⟩ w

theorem disc_origin_ray_mem_iff_klein (ξ : ℂ) (hξ : ‖ξ‖ = 1) (w : 𝔻) :
    w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ) ↔ _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w ∈ segment ℝ 0 ξ := by
  let p := Complex.UnitClosedDisc.mk ξ hξ.le
  have hp : ‖(p : ℂ)‖ = 1 := hξ
  have hpK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p = ξ :=
    congrArg (fun z : 𝕔𝔻 => (z : ℂ)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hp)
  have hzK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) = 0 := by
    change (2/(1+‖(0 : ℂ)‖^2)) • (0 : ℂ) = 0
    simp only [smul_zero]
  have hclosed := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay_isClosed (0 : 𝔻) (ξ : OnePoint ℂ)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hξ)
  have hrel : w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ) ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ)) := by
    rw [← mem_preimage, ← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage]
    change w ∈ _ ↔ w ∈ closure _
    rw [hclosed.closure_eq]
  rw [hrel]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w ∈ closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended p)) ↔ _
  rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_ray 0 p hp]
  have him := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel 0) p
  rw [hzK, hpK] at him
  rw [← him]
  constructor
  · exact fun h => ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w, h, rfl⟩
  · rintro ⟨q, hq, he⟩
    have he' : q = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] using he)
    exact he' ▸ hq

theorem disc_origin_ray_mem_iff_radial (ξ : ℂ) (hξ : ‖ξ‖ = 1) (w : 𝔻) :
    w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ) ↔
      ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ (w : ℂ) = t • ξ := by
  rw [disc_origin_ray_mem_iff_klein ξ hξ, segment_eq_image']
  simp only [sub_zero, zero_add]
  let c : ℝ := 2/(1+‖(w : ℂ)‖^2)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcoord : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate w = c • (w : ℂ) := rfl
  constructor
  · rintro ⟨t, ht, he⟩
    have hw : (w : ℂ) = (t/c) • ξ := by
      rw [hcoord] at he
      calc
        (w : ℂ) = c⁻¹ • (c • (w : ℂ)) := by rw [inv_smul_smul₀ hc.ne']
        _ = c⁻¹ • (t • ξ) := congrArg (c⁻¹ • ·) he.symm
        _ = (t/c) • ξ := by rw [smul_smul]; congr 1; ring
    have hn : ‖(w : ℂ)‖ = t/c := by
      rw [hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht.1 hc.le), hξ, mul_one]
    exact ⟨t/c, div_nonneg ht.1 hc.le, hn ▸ w.norm_lt_one, hw⟩
  · rintro ⟨t, ht, ht1, hw⟩
    have hn : ‖(w : ℂ)‖ = t := by
      rw [hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hξ, mul_one]
    have hct : c*t ≤ 1 := by
      dsimp only [c]
      rw [hn]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 1+t^2)).mpr
      nlinarith only [sq_nonneg (t-1)]
    refine ⟨c*t, ⟨mul_nonneg hc.le ht, hct⟩, ?_⟩
    rw [hcoord, hw, smul_smul]

theorem disc_boundary_rate_near_origin_ray (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (z : 𝔻) (K : ℝ) (hK : 0 ≤ K) (hz : ‖ξ-(z : ℂ)‖ ≤ K*(1-‖(z : ℂ)‖)) :
    ∃ p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z p ≤ Real.arcosh (1+2*(K+1)^2) := by
  let r := ‖(z : ℂ)‖
  have hr : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := z.norm_lt_one
  have hgap : 0 < 1-r := sub_pos.mpr hr1
  let p := Complex.UnitDisc.mk (r • ξ) (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hξ, mul_one]
    exact hr1)
  have hp : ‖(p : ℂ)‖ = r := by
    change ‖r • ξ‖ = r
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hξ, mul_one]
  have hδ : ‖(z : ℂ)-p‖ ≤ (K+1)*(1-r) := by
    have he : (z : ℂ)-p = ((z : ℂ)-ξ)+(1-r) • ξ := by
      change (z : ℂ)-r • ξ = _
      rw [sub_smul, one_smul]
      abel
    rw [he]
    calc
      _ ≤ ‖(z : ℂ)-ξ‖+‖(1-r) • ξ‖ := norm_add_le _ _
      _ = ‖ξ-(z : ℂ)‖+(1-r) := by
        rw [norm_sub_rev, norm_smul, Real.norm_eq_abs, abs_of_pos hgap, hξ, mul_one]
      _ ≤ K*(1-r)+(1-r) := add_le_add hz (le_refl _)
      _ = _ := by ring
  have hδsq : ‖(z : ℂ)-p‖^2 ≤ (K+1)^2*(1-r)^2 := by
    have h := mul_le_mul hδ hδ (norm_nonneg _) (by positivity : 0 ≤ (K+1)*(1-r))
    nlinarith only [h]
  have hgap2 : 0 < 1-r^2 := sub_pos.mpr z.sq_norm_lt_one
  have hcmp : 1-r ≤ 1-r^2 := by nlinarith only [mul_nonneg hr hgap.le]
  have hsquare : (1-r)^2 ≤ (1-r^2)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hcmp) (by positivity : 0 ≤ (1-r^2)+(1-r))]
  have hnum : ‖(z : ℂ)-p‖^2 ≤ (K+1)^2*((1-r^2)*(1-r^2)) := by
    calc
      _ ≤ (K+1)^2*(1-r)^2 := hδsq
      _ ≤ (K+1)^2*(1-r^2)^2 := mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = _ := by ring
  have hcos : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z p) ≤ 1+2*(K+1)^2 := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance, hp]
    change 1+2*‖(z : ℂ)-p‖^2/((1-r^2)*(1-r^2)) ≤ _
    have he : 2*‖(z : ℂ)-p‖^2/((1-r^2)*(1-r^2)) ≤ 2*(K+1)^2 :=
      (div_le_iff₀ (mul_pos hgap2 hgap2)).mpr (by nlinarith only [hnum])
    linarith only [he]
  refine ⟨p, (disc_origin_ray_mem_iff_radial ξ hξ p).mpr ⟨r, hr, hr1, rfl⟩, ?_⟩
  have h := (Real.arcosh_le_arcosh (Real.cosh_pos _) (by positivity : 0 < 1+2*(K+1)^2)).mpr hcos
  rwa [Real.arcosh_cosh (disc_pathDist_nonneg z p)] at h

theorem disc_boundary_rate_of_near_origin_ray (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (z p : 𝔻)
    (hp : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ))
    (M : ℝ)
    (hM : 0 ≤ M)
    (hd : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z p ≤ M) :
    ‖ξ-(z : ℂ)‖ ≤ 4*Real.cosh M*(1-‖(z : ℂ)‖) := by
  obtain ⟨t, ht, ht1, hpt⟩ := (disc_origin_ray_mem_iff_radial ξ hξ p).mp hp
  have hpn : ‖(p : ℂ)‖ = t := by
    rw [hpt, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hξ, mul_one]
  let a := 1-‖(z : ℂ)‖
  let b := 1-t
  let c := Real.cosh M
  let δ := ‖(z : ℂ)-p‖
  have ha : 0 < a := sub_pos.mpr z.norm_lt_one
  have hb : 0 < b := sub_pos.mpr ht1
  have hc : 1 ≤ c := Real.one_le_cosh _
  have hδ : 0 ≤ δ := norm_nonneg _
  have hcos : Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z p) ≤ c :=
    Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg (disc_pathDist_nonneg z p), abs_of_nonneg hM])
  have hgap : 0 < 1-‖(z : ℂ)‖^2 := sub_pos.mpr z.sq_norm_lt_one
  have htgap : 0 < 1-t^2 := by nlinarith only [ht, ht1]
  have hsq : 2*δ^2 ≤ (c-1)*((1-‖(z : ℂ)‖^2)*(1-t^2)) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_cosh_distance, hpn] at hcos
    have h := (div_le_iff₀ (mul_pos hgap htgap)).mp
      (show 2*δ^2/((1-‖(z : ℂ)‖^2)*(1-t^2)) ≤ c-1 by linarith only [hcos])
    exact h
  have hza : 1-‖(z : ℂ)‖^2 ≤ 2*a := by
    dsimp only [a]
    nlinarith only [sq_nonneg (1-‖(z : ℂ)‖)]
  have htb : 1-t^2 ≤ 2*b := by
    dsimp only [b]
    nlinarith only [sq_nonneg (1-t)]
  have hden : (1-‖(z : ℂ)‖^2)*(1-t^2) ≤ 4*a*b := by
    have h := mul_le_mul hza htb htgap.le (by positivity : 0 ≤ 2*a)
    nlinarith only [h]
  have hδsq : δ^2 ≤ 2*(c-1)*a*b := by
    have h := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hc)
    nlinarith only [hsq, h]
  have hrev : (b-a)^2 ≤ δ^2 := by
    have h := abs_norm_sub_norm_le (z : ℂ) (p : ℂ)
    rw [hpn] at h
    have hs := mul_le_mul h h (abs_nonneg _) hδ
    rw [← sq, sq_abs] at hs
    dsimp only [a, b]
    nlinarith only [hs]
  have hab : b ≤ 2*c*a := by
    by_contra h
    have he : 0 < b*(b-2*c*a) := mul_pos hb (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hrev, hδsq, he, sq_nonneg a]
  have hδbound : δ ≤ 2*c*a := by
    have hm := mul_le_mul_of_nonneg_left hab
      (by positivity : 0 ≤ 2*(c-1)*a)
    have hs : δ^2 ≤ (2*c*a)^2 := by
      have hh : 0 ≤ 4*c*a^2 := by positivity
      nlinarith only [hδsq, hm, hh]
    nlinarith only [hs, hδ, (show 0 < 2*c*a by positivity)]
  have hξp : ‖ξ-(p : ℂ)‖ = b := by
    have he : ξ-t • ξ = (1-t) • ξ := by rw [sub_smul, one_smul]
    rw [hpt, he, norm_smul, Real.norm_eq_abs, abs_of_pos hb, hξ, mul_one]
  calc
    _ = ‖(ξ-(p : ℂ))+((p : ℂ)-z)‖ := by congr 1; abel
    _ ≤ ‖ξ-(p : ℂ)‖+‖(p : ℂ)-z‖ := norm_add_le _ _
    _ = b+δ := by rw [hξp, norm_sub_rev]
    _ ≤ 4*c*a := by linarith only [hab, hδbound]

def approximationCanonicalRay
    (v : 𝔻)
    (ξ : ℂ)
    (hξ : ‖ξ‖ = 1) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v :=
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay v (ξ : OnePoint ℂ), (ξ : OnePoint ℂ),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hξ,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHLineRay_discHRay v _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hξ)⟩

theorem approximationCanonicalRay_endpoint (v : 𝔻) (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    (approximationCanonicalRay v ξ hξ).idealEndpoint = (ξ : OnePoint ℂ) := by
  obtain ⟨_, _, _, _, _, he⟩ := (approximationCanonicalRay v ξ hξ).isRay
  have h := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay_idealEndpoints v (ξ : OnePoint ℂ)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hξ)
  exact singleton_injective (he.symm.trans h)

theorem disc_sequence_radial_rate_iff_origin_ray (z : ℕ → 𝔻) (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    (fun n => ξ-(z n : ℂ)) =O[atTop] (fun n => 1-‖(z n : ℂ)‖) ↔
      (let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric;
        (fun n => Metric.infDist (z n) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ))) =O[atTop]
          (fun _ : ℕ => (1 : ℝ))) := by
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  constructor
  · intro h
    obtain ⟨C, hC, hb⟩ := bound_of_isBigO_nat_atTop h
    apply IsBigO.of_bound (Real.arcosh (1+2*(C+1)^2))
    apply Filter.Eventually.of_forall
    intro n
    have hr : ‖ξ-(z n : ℂ)‖ ≤ C*(1-‖(z n : ℂ)‖) := by
      have he := hb (x := n) (ne_of_gt (sub_pos.mpr (z n).norm_lt_one))
      simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (z n).norm_lt_one)] using he
    obtain ⟨p, hp, hd⟩ := disc_boundary_rate_near_origin_ray ξ hξ (z n) C hC.le hr
    rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg, norm_one, mul_one]
    exact (Metric.infDist_le_dist_of_mem hp).trans
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using hd)
  · intro h
    obtain ⟨C, hC⟩ := isBigO_one_nat_atTop_iff.mp h
    have hC0 : 0 ≤ C := Metric.infDist_nonneg.trans
      ((le_abs_self _).trans (hC 0))
    apply IsBigO.of_bound (4*Real.cosh (C+1))
    apply Filter.Eventually.of_forall
    intro n
    have hb : Metric.infDist (z n) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ)) < C+1 := by
      have he := hC n
      rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg] at he
      linarith only [he]
    have hne : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay 0 (ξ : OnePoint ℂ)).Nonempty :=
      ⟨0, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay_start_mem _ _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedDiscIdealBoundary ξ).mpr hξ)⟩
    obtain ⟨p, hp, hd⟩ := (Metric.infDist_lt_iff hne).mp hb
    have he := disc_boundary_rate_of_near_origin_ray ξ hξ (z n) p hp (C+1) (by positivity)
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using hd.le)
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr (z n).norm_lt_one)] using he

theorem bounded_infDist_transfer {X : Type*} [MetricSpace X] (x : ℕ → X)
    (R S : Set X) (hR : R.Nonempty) (M : ℝ)
    (hnear : ∀ p ∈ R, ∃ q ∈ S, dist p q ≤ M)
    (hbound : (fun n => Metric.infDist (x n) R) =O[atTop] (fun _ : ℕ => (1 : ℝ))) :
    (fun n => Metric.infDist (x n) S) =O[atTop] (fun _ : ℕ => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := isBigO_one_nat_atTop_iff.mp hbound
  apply IsBigO.of_bound (C+1+M)
  apply Filter.Eventually.of_forall
  intro n
  have hb : Metric.infDist (x n) R < C+1 := by
    have he := hC n
    rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg] at he
    linarith only [he]
  obtain ⟨p, hp, hd⟩ := (Metric.infDist_lt_iff hR).mp hb
  obtain ⟨q, hq, hpq⟩ := hnear p hp
  rw [Real.norm_eq_abs, abs_of_nonneg Metric.infDist_nonneg, norm_one, mul_one]
  calc
    _ ≤ dist (x n) q := Metric.infDist_le_dist_of_mem hq
    _ ≤ dist (x n) p+dist p q := dist_triangle _ _ _
    _ ≤ C+1+M := add_le_add hd.le hpq

theorem disc_sequence_ray_bound_iff_radial_rate (z : ℕ → 𝔻) (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {v : 𝔻}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v)
    (hR : R.idealEndpoint = (ξ : OnePoint ℂ)) :
    (let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric;
      (fun n => Metric.infDist (z n) R.val) =O[atTop] (fun _ : ℕ => (1 : ℝ))) ↔
        (fun n => ξ-(z n : ℂ)) =O[atTop] (fun n => 1-‖(z n : ℂ)‖) := by
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  let A := approximationCanonicalRay 0 ξ hξ
  have hA : A.idealEndpoint = (ξ : OnePoint ℂ) := approximationCanonicalRay_endpoint 0 ξ hξ
  constructor
  · intro h
    obtain ⟨M, _, hnear⟩ := same_endpoint_discRays_uniform_distance R A (hR.trans hA.symm)
    apply (disc_sequence_radial_rate_iff_origin_ray z ξ hξ).mpr
    exact bounded_infDist_transfer z R.val A.val ⟨v, R.start_mem⟩ M
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using hnear) h
  · intro h
    obtain ⟨M, _, hnear⟩ := same_endpoint_discRays_uniform_distance A R (hA.trans hR.symm)
    exact bounded_infDist_transfer z A.val R.val ⟨0, A.start_mem⟩ M
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using hnear)
      ((disc_sequence_radial_rate_iff_origin_ray z ξ hξ).mp h)

theorem disc_orbit_matrix_rate_iff_ray_bound
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) (hξ : ‖ξ‖ = 1) (w : 𝔻)
    {v : 𝔻}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v)
    (hR : R.idealEndpoint = (ξ : OnePoint ℂ)) :
    HasDiscOrbitMatrixRate P g ξ w ↔
      (let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric;
        (fun n => Metric.infDist (P.discAction (g n) w) R.val) =O[atTop]
          (fun _ : ℕ => (1 : ℝ))) :=
  (disc_orbit_matrix_iff_euclidean_radial_rate P g ξ w).trans
    (disc_sequence_ray_bound_iff_radial_rate (fun n => P.discAction (g n) w) ξ hξ R hR).symm

/-- Statement (2), using the true metric distance to every genuine ending ray. -/
def HasDiscOrbitRayBound {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) : Prop :=
  ∀ (w v : 𝔻) (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v), R.idealEndpoint = (ξ : OnePoint ℂ) →
    (let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric;
      (fun n => Metric.infDist (P.discAction (g n) w) R.val) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)))

/-- Statement (3) uses a compact set in the original disc topology and actual inverse ray images. -/
def HasDiscOrbitCompactRayIntersection {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) : Prop :=
  ∀ (v : 𝔻) (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v), R.idealEndpoint = (ξ : OnePoint ℂ) →
    ∃ K : Set 𝔻, IsCompact K ∧ ∀ n : ℕ, ((P.discAction (g n)) ⁻¹' R.val ∩ K).Nonempty

theorem disc_orbit_all_rates_iff_ray_bound
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    (∀ w : 𝔻, HasDiscOrbitMatrixRate P g ξ w) ↔ HasDiscOrbitRayBound P g ξ := by
  constructor
  · intro h w v R hR
    exact (disc_orbit_matrix_rate_iff_ray_bound P g ξ hξ w R hR).mp (h w)
  · intro h w
    let R := approximationCanonicalRay 0 ξ hξ
    have hR := approximationCanonicalRay_endpoint 0 ξ hξ
    exact (disc_orbit_matrix_rate_iff_ray_bound P g ξ hξ w R hR).mpr (h w 0 R hR)

theorem disc_orbit_ray_bound_iff_compact {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (ξ : ℂ) :
    HasDiscOrbitRayBound P g ξ ↔ HasDiscOrbitCompactRayIntersection P g ξ := by
  constructor
  · intro h v R hR
    exact (disc_orbit_ray_infDist_iff_compact P g R 0).mp (h 0 v R hR)
  · intro h w v R hR
    exact (disc_orbit_ray_infDist_iff_compact P g R w).mpr (h v R hR)

/-- The original theorem, with the genuine limit set, distinct original group elements,
all actual interior basepoints, all actual ending half-rays, and original compact sets. -/
theorem orbitMatrixRate_iff_rayBound_and_compactRayIntersection
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : ℕ → H) (_hg : Function.Injective g)
    (ξ : ℂ) (hξ : (ξ : OnePoint ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianLimitSet H) :
    ((∀ w : 𝔻, HasDiscOrbitMatrixRate P g ξ w) ↔ HasDiscOrbitRayBound P g ξ) ∧
      ((∀ w : 𝔻, HasDiscOrbitMatrixRate P g ξ w) ↔ HasDiscOrbitCompactRayIntersection P g ξ) := by
  have he := disc_orbit_all_rates_iff_ray_bound P g ξ (fuchsian_limit_finite_norm_one P ξ hξ)
  exact ⟨he, he.trans (disc_orbit_ray_bound_iff_compact P g ξ)⟩

end LowDimensionalTopology.Geometry.Fuchsian
