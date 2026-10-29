module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disk.SchwarzPick
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk

/-!
# Schwarz--Pick for the actual Poincare path distance

The metric is the existing infimum of literal density-weighted curve lengths.
The proof compares Blaschke cross ratios, then uses the proved distance formula.
-/

@[expose] public section
noncomputable section

open Set Metric Complex Filter Topology
open scoped ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

open LiZhongQC

/-- Restrict an actual holomorphic disk self-map to the disk carrier. -/
def discSelfMap (f : ℂ → ℂ) (hm : MapsTo f unitDisc unitDisc) : 𝔻 → 𝔻 :=
  fun z => ⟨f z, hm z.property⟩

/-- Schwarz--Pick in the invariant cross-ratio form. -/
theorem disc_schwarz_pick_blaschke {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc)
    {z w : ℂ} (hz : z ∈ unitDisc) (hw : w ∈ unitDisc) :
    ‖blaschke (f z) (f w)‖ ≤ ‖blaschke z w‖ := by
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have hfz : ‖f z‖ < 1 := mem_ball_zero_iff.mp (hm hz)
  have hi : MapsTo (blaschke (-z)) unitDisc unitDisc := fun t ht =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc (by simpa using hz')
      (mem_ball_zero_iff.mp ht))
  have ho : MapsTo (blaschke (f z)) unitDisc unitDisc := fun t ht =>
    mem_ball_zero_iff.mpr (blaschke_mem_unitDisc hfz (mem_ball_zero_iff.mp ht))
  have hd : DifferentiableOn ℂ (discNormalizedMap f z) unitDisc :=
    (differentiableOn_blaschke hfz).comp
      (hf.comp (differentiableOn_blaschke (by simpa using hz')) hi) (hm.comp hi)
  have hmap : MapsTo (discNormalizedMap f z) (ball 0 1) (closedBall 0 1) :=
    fun t ht => ball_subset_closedBall (ho (hm (hi ht)))
  have hzero : discNormalizedMap f z 0 = 0 := by
    simp [discNormalizedMap, blaschke]
  have hb := Complex.norm_le_norm_of_mapsTo_ball hd hmap hzero
    (blaschke_mem_unitDisc hz' hw')
  simpa only [discNormalizedMap, Function.comp_apply, blaschke_neg_blaschke hz' hw'] using hb

theorem disc_tanh_half_distance_eq_blaschke (z w : 𝔻) :
    Real.tanh (discPathDist z w / 2) = ‖blaschke w z‖ := by
  rw [disc_tanh_half_distance, blaschke, norm_div, mul_comm (conj (w : ℂ)) (z : ℂ)]

/-- Every holomorphic disk self-map contracts the actual Poincare path distance. -/
theorem disc_schwarz_pick_distance {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc)
    (z w : 𝔻) :
    discPathDist (discSelfMap f hm z) (discSelfMap f hm w) ≤ discPathDist z w := by
  have hb := disc_schwarz_pick_blaschke hf hm w.property z.property
  have ht : Real.tanh (discPathDist (discSelfMap f hm z) (discSelfMap f hm w) / 2) ≤
      Real.tanh (discPathDist z w / 2) := by
    rw [disc_tanh_half_distance_eq_blaschke, disc_tanh_half_distance_eq_blaschke]
    exact hb
  have ha := Real.artanh_le_artanh (Real.neg_one_lt_tanh _)
    (Real.tanh_lt_one _) ht
  rw [Real.artanh_tanh, Real.artanh_tanh] at ha
  linarith

/-- Disk automorphisms attain infinitesimal equality at every point. -/
theorem disc_schwarz_pick_eq_of_conformal {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc unitDisc) {z : ℂ} (hz : z ∈ unitDisc) :
    ‖deriv f z‖ * (1 - ‖z‖ ^ 2) = 1 - ‖f z‖ ^ 2 := by
  let g := Function.invFunOn f unitDisc
  have hg : IsConformalOnto g unitDisc unitDisc := hf.symm isOpen_ball
  have hm : MapsTo f unitDisc unitDisc := fun _ hx => hf.2.2 ▸ mem_image_of_mem f hx
  have hgm : MapsTo g unitDisc unitDisc := fun _ hx => hg.2.2 ▸ mem_image_of_mem g hx
  have hleft : g (f z) = z := hf.2.1.leftInvOn_invFunOn hz
  have hcomp := ((hg.1.differentiableAt (isOpen_ball.mem_nhds (hm hz))).hasDerivAt).comp z
    ((hf.1.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt)
  have heq : (g ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with t ht
    exact hf.2.1.leftInvOn_invFunOn ht
  have hprod : deriv g (f z) * deriv f z = 1 := by
    rw [← hcomp.deriv, heq.deriv_eq, deriv_id]
  have hnorm : ‖deriv g (f z)‖ * ‖deriv f z‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hback := disc_schwarz_pick_cross hg.1 hgm (hm hz)
  rw [hleft] at hback
  have hmul := mul_le_mul_of_nonneg_right hback (norm_nonneg (deriv f z))
  apply le_antisymm (disc_schwarz_pick_cross hf.1 hm hz)
  calc
    1 - ‖f z‖ ^ 2 = (‖deriv g (f z)‖ * ‖deriv f z‖) * (1 - ‖f z‖ ^ 2) := by
      rw [hnorm, one_mul]
    _ = (‖deriv g (f z)‖ * (1 - ‖f z‖ ^ 2)) * ‖deriv f z‖ := by ring
    _ ≤ (1 - ‖z‖ ^ 2) * ‖deriv f z‖ := hmul
    _ = ‖deriv f z‖ * (1 - ‖z‖ ^ 2) := mul_comm _ _

/-- Equality at one point is equivalent to equality everywhere and to being
a biholomorphic automorphism, with no chosen inverse added to the hypotheses. -/
theorem disc_isConformalOnto_iff_schwarz_pick_eq {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hm : MapsTo f unitDisc unitDisc) :
    IsConformalOnto f unitDisc unitDisc ↔
      ∀ z ∈ unitDisc, ‖deriv f z‖ * (1 - ‖z‖ ^ 2) = 1 - ‖f z‖ ^ 2 := by
  constructor
  · exact fun h z hz => disc_schwarz_pick_eq_of_conformal h hz
  · intro h
    exact disc_schwarz_pick_rigidity hf hm (mem_ball_self one_pos) (h 0 (mem_ball_self one_pos))

end LowDimensionalTopology.Geometry.Hyperbolic
