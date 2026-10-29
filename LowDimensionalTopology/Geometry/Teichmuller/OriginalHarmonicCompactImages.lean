module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHarmonicBiparameterFamily
public import LowDimensionalTopology.External.LiZhongQC.Ch05.S21_UniversalTeichmuller
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Uniform compact image control for the actual harmonic family

Normalized quasiconformal growth and parameter Cauchy estimates give
uniform closeness on bounded sets. Inverse growth then controls the
preimages of disks near a compact subset of the upper half-plane.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Topology Metric
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation

open Surfaces GammaMeasurableBeltrami LiZhongQC

private theorem norm_sub_zero_le_of_holomorphic_bound
    {g : ℂ → ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hg : DifferentiableOn ℂ g (ball 0 δ))
    (hM : ∀ v ∈ ball 0 δ, ‖g v‖ ≤ M)
    {s : ℂ} (hs : ‖s‖ < δ / 2) :
    ‖g s - g 0‖ ≤ M / (δ / 2) * ‖s‖ := by
  have hd (w : ℂ) (hw : w ∈ ball 0 (δ / 2)) :
      ‖deriv g w‖ ≤ M / (δ / 2) := by
    have hsub : closedBall w (δ / 2) ⊆ ball 0 δ := by
      intro v hv
      rw [mem_closedBall] at hv
      rw [mem_ball] at hw ⊢
      linarith [dist_triangle v w 0]
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hg.diffContOnCl_ball hsub)
      (fun v hv => hM v (hsub (sphere_subset_closedBall hv)))
  have hdiff (w : ℂ) (hw : w ∈ ball 0 (δ / 2)) : DifferentiableAt ℂ g w :=
    hg.differentiableAt (isOpen_ball.mem_nhds
      ((ball_subset_ball (by linarith : δ / 2 ≤ δ)) hw))
  have h := (convex_ball (0 : ℂ) (δ / 2)).norm_image_sub_le_of_norm_deriv_le
    hdiff hd (mem_ball_self (by positivity)) (mem_ball_zero_iff.mpr hs)
  simpa only [sub_zero] using h

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)

/-- The same parameter window gives normalized distortion control and
linear closeness to the identity on every bounded spatial set. -/
theorem canonicalBiparameterFamily_bounded_closeness
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
        IsKQCNormalizedPlane (canonicalBiparameterFamily R p q s t) 3) ∧
      ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧
        ∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε → ∀ z : ℂ, ‖z‖ ≤ B →
          ‖canonicalBiparameterFamily R p q s t z - z‖ ≤
            C * (‖s‖ + ‖t‖) := by
  obtain ⟨δ, hδ, hspec, hfirst, hsecond⟩ :=
    canonicalBiparameterFamily_separately_holomorphic R p hp q
  have hsharp (s t : ℂ) (hs : ‖s‖ < δ) (ht : ‖t‖ < δ) :
      IsKQCNormalizedPlane (canonicalBiparameterFamily R p q s t) 3 := by
    obtain ⟨_, _, hK, huniq⟩ := thm13_7_normalized_existence
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      (hspec s t hs ht).1
    have hsol := (hspec s t hs ht).2
    refine ⟨?_, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1⟩
    rw [huniq _ hsol]
    simpa only [show (1 + (1 / 2 : ℝ)) / (1 - 1 / 2) = 3 by norm_num] using hK
  have hzero : canonicalBiparameterFamily R p q 0 0 = id := by
    simpa only [map_zero] using
      (canonicalBiparameterFamily_diagonal R p q 0).trans (canonicalFamily_zero R p q)
  have h0 : ‖(0 : ℂ)‖ < δ := by simpa only [norm_zero] using hδ
  refine ⟨δ / 2, by positivity,
    fun s t hs ht => hsharp s t (by linarith) (by linarith), ?_⟩
  intro B hB
  let M : ℝ := max (lambdaInv (3 * quadLambda B)) 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨M / (δ / 2), by positivity, ?_⟩
  intro s t hs ht z hz
  have htδ : ‖t‖ < δ := by linarith
  have hbound (a b : ℂ) (ha : ‖a‖ < δ) (hb : ‖b‖ < δ) :
      ‖canonicalBiparameterFamily R p q a b z‖ ≤ M :=
    (UniversalTeichmuller.ut2_nb_upper (hsharp a b ha hb) hB hz).trans (le_max_left _ _)
  have h₁ := norm_sub_zero_le_of_holomorphic_bound hδ (hfirst t htδ z)
    (fun a ha => hbound a t (mem_ball_zero_iff.mp ha) htδ) hs
  have h₂ := norm_sub_zero_le_of_holomorphic_bound hδ (hsecond 0 h0 z)
    (fun b hb => hbound 0 b h0 (mem_ball_zero_iff.mp hb)) ht
  have h₂' : ‖canonicalBiparameterFamily R p q 0 t z - z‖ ≤
      M / (δ / 2) * ‖t‖ := by
    simpa only [hzero, id_eq] using h₂
  calc
    ‖canonicalBiparameterFamily R p q s t z - z‖ ≤
        ‖canonicalBiparameterFamily R p q s t z -
          canonicalBiparameterFamily R p q 0 t z‖ +
        ‖canonicalBiparameterFamily R p q 0 t z - z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ M / (δ / 2) * ‖s‖ + M / (δ / 2) * ‖t‖ := add_le_add h₁ h₂'
    _ = M / (δ / 2) * (‖s‖ + ‖t‖) := by ring

/-- A compact source set has uniformly separated images from the closed
lower half-plane and genuine fixed-radius image disks. The actual inverse
on those disks also has a uniform bound. -/
theorem canonicalBiparameterFamily_compact_image_control
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (K : Set ℍ) (hK : IsCompact K) :
    ∃ ε d B : ℝ, 0 < ε ∧ 0 < d ∧ 0 < B ∧
      ∀ s t : ℂ, ‖s‖ < ε → ‖t‖ < ε →
        let f := canonicalBiparameterFamily R p q s t
        IsKQCNormalizedPlane f 3 ∧ ∀ z ∈ K,
          ‖f (z : ℂ)‖ ≤ B ∧
          (∀ w : ℂ, w.im ≤ 0 → d ≤ ‖f (z : ℂ) - f w‖) ∧
          closedBall (z : ℂ) d ⊆ f '' upperHalf ∧
          closedBall (f (z : ℂ)) d ⊆ f '' upperHalf ∧
          ∀ w ∈ closedBall (f (z : ℂ)) d,
            ‖Function.invFunOn f upperHalf w‖ ≤ B := by
  obtain ⟨δ, hδ, hsharp, hlinear⟩ :=
    canonicalBiparameterFamily_bounded_closeness R p hp q
  obtain ⟨h, hh, hheight⟩ := hK.exists_forall_le'
    UpperHalfPlane.continuous_im.continuousOn (fun z _ => z.im_pos)
  obtain ⟨b, hb⟩ := hK.bddAbove_image UpperHalfPlane.continuous_coe.norm.continuousOn
  let B₀ : ℝ := max b 1
  have hB₀ : 0 < B₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hnorm (z : ℍ) (hz : z ∈ K) : ‖(z : ℂ)‖ ≤ B₀ :=
    (hb (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  let T : ℝ := B₀ + h + 1
  have hT : 0 < T := by dsimp only [T]; positivity
  let L : ℝ := lambdaInv (3 * quadLambda T)
  let S : ℝ := max B₀ (max L 1)
  have hS : 0 < S := hB₀.trans_le (le_max_left _ _)
  have hLS : L ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨C, hC, hlin⟩ := hlinear S hS
  refine ⟨min δ (h / (16 * C)), h / 8, max T S,
    lt_min hδ (by positivity), by positivity, hT.trans_le (le_max_left _ _), ?_⟩
  intro s t hs ht
  dsimp only
  let f := canonicalBiparameterFamily R p q s t
  have hsδ : ‖s‖ < δ := hs.trans_le (min_le_left _ _)
  have htδ : ‖t‖ < δ := ht.trans_le (min_le_left _ _)
  have hqc : IsKQCNormalizedPlane f 3 := hsharp s t hsδ htδ
  have hsC : ‖s‖ * (16 * C) < h :=
    (lt_div_iff₀ (by positivity : 0 < 16 * C)).mp (hs.trans_le (min_le_right _ _))
  have htC : ‖t‖ * (16 * C) < h :=
    (lt_div_iff₀ (by positivity : 0 < 16 * C)).mp (ht.trans_le (min_le_right _ _))
  have hsmall : C * (‖s‖ + ‖t‖) < h / 8 := by nlinarith
  have hclose (w : ℂ) (hw : ‖w‖ ≤ S) : ‖f w - w‖ < h / 8 :=
    (hlin s t hsδ htδ w hw).trans_lt hsmall
  refine ⟨hqc, ?_⟩
  intro z hz
  have hzS : ‖(z : ℂ)‖ ≤ S := (hnorm z hz).trans (le_max_left _ _)
  have hzclose := hclose (z : ℂ) hzS
  have hfz : ‖f (z : ℂ)‖ ≤ B₀ + h / 8 := by
    linarith [norm_sub_norm_le (f (z : ℂ)) (z : ℂ), hnorm z hz]
  have hnear (u : ℂ) (hu : ‖f u - f (z : ℂ)‖ ≤ h / 4) :
      0 < u.im ∧ ‖u‖ ≤ S := by
    have hfu : ‖f u‖ ≤ T := by
      dsimp only [T]
      linarith [norm_sub_norm_le (f u) (f (z : ℂ))]
    have huL : ‖u‖ ≤ L := UniversalTeichmuller.ut2_nb_lower hqc hT hfu
    have huS : ‖u‖ ≤ S := huL.trans hLS
    have huclose := hclose u huS
    have hi₁ := Complex.im_le_norm ((z : ℂ) - f (z : ℂ))
    have hi₂ := Complex.im_le_norm (f (z : ℂ) - f u)
    have hi₃ := Complex.im_le_norm (f u - u)
    rw [Complex.sub_im, norm_sub_rev] at hi₁ hi₂
    rw [Complex.sub_im] at hi₃
    exact ⟨by linarith [show h ≤ (z : ℂ).im from hheight z hz], huS⟩
  have hball : closedBall (f (z : ℂ)) (h / 4) ⊆ f '' upperHalf := by
    intro w hw
    have hwuniv : w ∈ f '' univ := by rw [hqc.2.1]; exact mem_univ w
    obtain ⟨u, _, hu⟩ := hwuniv
    have hdist : ‖f u - f (z : ℂ)‖ ≤ h / 4 := by
      rw [hu]
      simpa only [mem_closedBall, dist_eq_norm] using hw
    exact ⟨u, (hnear u hdist).1, hu⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (show ‖f (z : ℂ)‖ ≤ T by dsimp only [T]; linarith).trans
    exact le_max_left _ _
  · intro w hw
    by_contra hsep
    have hdist : ‖f w - f (z : ℂ)‖ ≤ h / 4 := by
      rw [norm_sub_rev]
      linarith [lt_of_not_ge hsep]
    exact (not_lt_of_ge hw) (hnear w hdist).1
  · intro w hw
    apply hball
    have hw' : ‖w - (z : ℂ)‖ ≤ h / 8 := by
      simpa only [mem_closedBall, dist_eq_norm] using hw
    have hzrev : ‖(z : ℂ) - f (z : ℂ)‖ < h / 8 := by
      rwa [norm_sub_rev]
    rw [mem_closedBall, dist_eq_norm]
    have htri := norm_sub_le_norm_sub_add_norm_sub w (z : ℂ) (f (z : ℂ))
    linarith
  · exact (closedBall_subset_closedBall (by linarith : h / 8 ≤ h / 4)).trans hball
  · intro w hw
    have hwb : w ∈ closedBall (f (z : ℂ)) (h / 4) :=
      (closedBall_subset_closedBall (by linarith : h / 8 ≤ h / 4)) hw
    have hpre := Function.invFunOn_eq (hball hwb)
    have hdist : ‖f (Function.invFunOn f upperHalf w) - f (z : ℂ)‖ ≤ h / 4 := by
      rw [hpre]
      simpa only [mem_closedBall, dist_eq_norm] using hwb
    exact (hnear _ hdist).2.trans (le_max_right _ _)

end LowDimensionalTopology.Geometry.Teichmuller.HarmonicFirstVariation
