/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.Conventions
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.DensityMetric
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicCore
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareExtension
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.CurveLength
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic

/-!
# The upper-half-space length metric in finite dimensions

The density is the reciprocal of height. Its curve and chain lengths define the intrinsic
metric and are invariant under the Poincaré extension of boundary Möbius maps.

Vertical two-plane embeddings compare this metric with the upper-half-plane metric. The
comparison gives distance and sphere formulas, then triangle-equality intervals and unique
minimizing traces. The geometry statements require a horizontal direction; the density and
metric constructions also cover the zero-dimensional horizontal space.
-/

@[expose] public section

open Set Filter MeasureTheory Manifold NormedSpace
open scoped Topology ContDiff ENNReal OnePoint InnerProductSpace

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- The last Euclidean coordinate is the height in the upper-half-space model. -/
def halfSpaceHeight (n : ℕ) : Inversive.Euclidean (n + 1) →L[ℝ] ℝ :=
  EuclideanSpace.proj (Fin.last n)

theorem halfSpaceHeight_apply (n : ℕ) (x : Inversive.Euclidean (n + 1)) :
    halfSpaceHeight n x = x (Fin.last n) := rfl

/-- The actual open Euclidean upper half-space, using the project's L2 coordinates. -/
def upperHalfSpaceDomain (n : ℕ) : TopologicalSpace.Opens (Inversive.Euclidean (n + 1)) where
  carrier := Auxiliary.Analysis.upperHalfSpace n
  is_open' := isOpen_lt continuous_const (halfSpaceHeight n).continuous

abbrev HyperbolicHalfSpace (n : ℕ) := upperHalfSpaceDomain n

theorem mem_upperHalfSpaceDomain (n : ℕ) (x : Inversive.Euclidean (n + 1)) :
    x ∈ upperHalfSpaceDomain n ↔ 0 < halfSpaceHeight n x := Iff.rfl

theorem convex_upperHalfSpaceDomain (n : ℕ) :
    Convex ℝ (upperHalfSpaceDomain n : Set (Inversive.Euclidean (n + 1))) :=
  (convex_Ioi (0 : ℝ)).linear_preimage (halfSpaceHeight n).toLinearMap

instance hyperbolicHalfSpacePreconnected (n : ℕ) : PreconnectedSpace (HyperbolicHalfSpace n) :=
  Subtype.preconnectedSpace (convex_upperHalfSpaceDomain n).isPreconnected

/-- The positive continuous density is exactly the reciprocal of height. -/
def halfSpaceDensity (n : ℕ) : Auxiliary.Analysis.Density (upperHalfSpaceDomain n) where
  toFun x := 1 / halfSpaceHeight n x
  continuous := continuous_const.div
    ((halfSpaceHeight n).continuous.comp continuous_subtype_val)
    (fun x => (show 0 < halfSpaceHeight n x from x.property).ne')
  positive x := one_div_pos.mpr x.property

theorem halfSpaceDensity_apply (n : ℕ) (x : HyperbolicHalfSpace n) :
    halfSpaceDensity n x = 1 / (x.val (Fin.last n)) := rfl

/-- The actual Riemannian piece length; its next formula identifies the ordinary coordinate integral. -/
def halfSpacePieceLength {n : ℕ} (γ : ℝ → HyperbolicHalfSpace n) (a b : ℝ) : ℝ≥0∞ :=
  (halfSpaceDensity n).pieceLength γ a b

theorem halfSpacePieceLength_eq_coordinate_integral {n : ℕ}
    (γ : ℝ → HyperbolicHalfSpace n) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1 γ (Icc a b)) :
    halfSpacePieceLength γ a b = ENNReal.ofReal
      (∫ t in a..b, ‖derivWithin (fun s => (γ s).val) (Icc a b) t‖ /
        (γ t).val (Fin.last n)) := by
  rw [halfSpacePieceLength, (halfSpaceDensity n).pieceLength_eq_ofReal_integral γ a b hab hγ]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [halfSpaceDensity_apply]
  ring

/-- Every finite C1 chain has the sum of its actual density-weighted piece lengths. -/
def halfSpaceChainLength {n : ℕ} {x y : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) x y) : ℝ≥0∞ :=
  (halfSpaceDensity n).chainLength c

/-- The extended distance is constructed from the length-infimum Riemannian metric. -/
def halfSpacePathEDist {n : ℕ} (x y : HyperbolicHalfSpace n) : ℝ≥0∞ :=
  (halfSpaceDensity n).pathEDist x y

/-- The hyperbolic distance is the genuine real length-infimum distance. -/
def halfSpacePathDist {n : ℕ} (x y : HyperbolicHalfSpace n) : ℝ :=
  (halfSpaceDensity n).pathDist x y

theorem halfSpacePathEDist_eq_iInf_chainLengths {n : ℕ} (x y : HyperbolicHalfSpace n) :
    halfSpacePathEDist x y = ⨅ c : Auxiliary.Analysis.RiemannianC1Chain
      𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) x y, halfSpaceChainLength c := by
  exact (halfSpaceDensity n).pathEDist_eq_piecewiseEDist x y

theorem halfSpacePathDist_eq_sInf_chainLengths {n : ℕ} (x y : HyperbolicHalfSpace n) :
    halfSpacePathDist x y = sInf (Set.range (fun c : Auxiliary.Analysis.RiemannianC1Chain
      𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) x y => (halfSpaceChainLength c).toReal)) :=
  (halfSpaceDensity n).pathDist_eq_sInf_chain_lengths x y

/-- The metric structure comes from the proved density-length construction. -/
@[instance_reducible]
def halfSpaceMetricSpace (n : ℕ) : MetricSpace (HyperbolicHalfSpace n) :=
  (halfSpaceDensity n).metricSpace

theorem halfSpaceMetricSpace_dist {n : ℕ} (x y : HyperbolicHalfSpace n) :
    @dist (HyperbolicHalfSpace n) (halfSpaceMetricSpace n).toDist x y = halfSpacePathDist x y :=
  ((halfSpaceDensity n).pathDist_eq_dist x y).symm

/-- The length metric induces exactly the inherited Euclidean topology. -/
theorem halfSpaceMetricSpace_topology (n : ℕ) :
    (halfSpaceMetricSpace n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (HyperbolicHalfSpace n)) := rfl

theorem halfSpacePathEDist_ne_top {n : ℕ} (x y : HyperbolicHalfSpace n) :
    halfSpacePathEDist x y ≠ ⊤ := (halfSpaceDensity n).pathEDist_ne_top x y

/-- The distance satisfies all metric axioms for the actual finite-dimensional half-space. -/
theorem halfSpacePathDist_metric_axioms {n : ℕ} (x y z : HyperbolicHalfSpace n) :
    0 ≤ halfSpacePathDist x y ∧ (halfSpacePathDist x y = 0 ↔ x = y) ∧
    halfSpacePathDist x y = halfSpacePathDist y x ∧
    halfSpacePathDist x z ≤ halfSpacePathDist x y + halfSpacePathDist y z := by
  simp only [← halfSpaceMetricSpace_dist]
  exact ⟨@dist_nonneg _ (halfSpaceMetricSpace n).toPseudoMetricSpace x y,
    @dist_eq_zero _ (halfSpaceMetricSpace n) x y,
    @dist_comm _ (halfSpaceMetricSpace n).toPseudoMetricSpace x y,
    @dist_triangle _ (halfSpaceMetricSpace n).toPseudoMetricSpace x y z⟩

/-- Finite positive-height points identify with the genuine extended positive half-space. -/
def halfSpaceExtendedHomeomorph (n : ℕ) :
    HyperbolicHalfSpace n ≃ₜ poincareHalfSpaceSet n 1 :=
  (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage
    (upperHalfSpaceDomain n : Set (Inversive.Euclidean (n + 1)))).trans
    (Homeomorph.setCongr (by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, by change 0 < x (Fin.last n) at hx; simpa using hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, by change 0 < x (Fin.last n); simpa using hx, rfl⟩))

theorem halfSpaceExtendedHomeomorph_apply {n : ℕ} (x : HyperbolicHalfSpace n) :
    (halfSpaceExtendedHomeomorph n x).val = (x.val : Inversive.ExtendedEuclidean (n + 1)) := rfl

theorem halfSpaceExtendedHomeomorph_symm_apply {n : ℕ}
    (z : poincareHalfSpaceSet n 1) :
    (((halfSpaceExtendedHomeomorph n).symm z).val : Inversive.ExtendedEuclidean (n + 1)) = z.val := by
  exact congrArg Subtype.val ((halfSpaceExtendedHomeomorph n).apply_symm_apply z)

/-- Restriction of an actual extended homeomorphism preserving the positive half-space. -/
def halfSpaceHomeomorph {n : ℕ} (F : Inversive.ExtendedHomeomorph (n + 1))
    (hF : F '' poincareHalfSpaceSet n 1 = poincareHalfSpaceSet n 1) :
    HyperbolicHalfSpace n ≃ₜ HyperbolicHalfSpace n :=
  (halfSpaceExtendedHomeomorph n).trans
    ((F.image (poincareHalfSpaceSet n 1)).trans
      ((Homeomorph.setCongr hF).trans (halfSpaceExtendedHomeomorph n).symm))

theorem halfSpaceHomeomorph_apply {n : ℕ} (F : Inversive.ExtendedHomeomorph (n + 1))
    (hF : F '' poincareHalfSpaceSet n 1 = poincareHalfSpaceSet n 1)
    (x : HyperbolicHalfSpace n) :
    ((halfSpaceHomeomorph F hF x).val : Inversive.ExtendedEuclidean (n + 1)) = F x.val := by
  exact halfSpaceExtendedHomeomorph_symm_apply _

/-- The canonical native reflection-generated Poincaré extension on finite positive points. -/
def poincareHalfSpaceHomeomorph {n : ℕ} [NeZero n] (g : Inversive.GM n) :
    HyperbolicHalfSpace n ≃ₜ HyperbolicHalfSpace n :=
  halfSpaceHomeomorph (poincareExtension g : Inversive.ExtendedHomeomorph (n + 1))
    (poincareExtension_preservesHalfSpaces g 1)

theorem poincareHalfSpaceHomeomorph_apply {n : ℕ} [NeZero n] (g : Inversive.GM n)
    (x : HyperbolicHalfSpace n) :
    ((poincareHalfSpaceHomeomorph g x).val : Inversive.ExtendedEuclidean (n + 1)) =
      (poincareExtension g : Inversive.ExtendedHomeomorph (n + 1)) x.val :=
  halfSpaceHomeomorph_apply _ _ x

/-- Only a limit of normed secants is needed for the sharp distance-slope estimate. -/
theorem halfSpace_distance_right_slope_bound {n : ℕ}
    {δ : ℝ → HyperbolicHalfSpace n} {t L : ℝ} (hL : 0 ≤ L)
    (hslope : Tendsto (fun s => ‖slope (fun u => (δ u).val) t s‖)
      (𝓝[>] t) (𝓝 L))
    (hδc : ContinuousWithinAt δ (Ioi t) t)
    (p : HyperbolicHalfSpace n) {r : ℝ}
    (hr : halfSpaceDensity n (δ t) * L < r) :
    ∃ᶠ s in 𝓝[>] t, slope (fun s => halfSpacePathDist p (δ s)) t s < r := by
  let ρ := halfSpaceDensity n
  obtain ⟨C, hC, hCr⟩ : ∃ C : ℝ, ρ (δ t) < C ∧ C * L < r := by
    by_cases hzero : L = 0
    · exact ⟨ρ (δ t) + 1, by linarith, by simpa [hzero] using hr⟩
    · have hLp := lt_of_le_of_ne hL (Ne.symm hzero)
      obtain ⟨C, hC, hCr⟩ := exists_between ((lt_div_iff₀ hLp).mpr hr)
      exact ⟨C, hC, (lt_div_iff₀ hLp).mp hCr⟩
  have hd : ∀ᶠ s in 𝓝[>] t,
      ρ.pathDist (δ t) (δ s) ≤ C * ‖(δ s).val - (δ t).val‖ :=
    hδc (ρ.pathDist_eventually_le_norm (δ t) hC)
  have hquot : ∀ᶠ s in 𝓝[>] t,
      C * ‖slope (fun u => (δ u).val) t s‖ < r :=
    (tendsto_const_nhds.mul hslope) (Iio_mem_nhds hCr)
  apply Filter.Eventually.frequently
  filter_upwards [hd, hquot, self_mem_nhdsWithin] with s hs hq hst
  have hpos : 0 < s - t := sub_pos.mpr hst
  have htri : ρ.pathDist p (δ s) - ρ.pathDist p (δ t) ≤ ρ.pathDist (δ t) (δ s) := by
    have hh := ρ.pathDist_triangle p (δ t) (δ s)
    linarith
  calc
    slope (fun s => halfSpacePathDist p (δ s)) t s
      ≤ ρ.pathDist (δ t) (δ s) / (s - t) := by
        rw [slope_def_field]
        exact div_le_div_of_nonneg_right htri hpos.le
    _ ≤ (C * ‖(δ s).val - (δ t).val‖) / (s - t) :=
      div_le_div_of_nonneg_right hs hpos.le
    _ = C * ‖slope (fun u => (δ u).val) t s‖ := by
      simp only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hpos]
      ring
    _ < r := hq

/-- A continuous curve with a continuous norm-speed bound controls the genuine path distance. -/
theorem halfSpacePathDist_le_integral_of_normslope {n : ℕ}
    (δ : ℝ → HyperbolicHalfSpace n) (L : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hδ : ContinuousOn δ (Icc a b))
    (hL : ∀ t ∈ Ico a b, 0 ≤ L t)
    (hslope : ∀ t ∈ Ico a b,
      Tendsto (fun s => ‖slope (fun u => (δ u).val) t s‖) (𝓝[>] t) (𝓝 (L t)))
    (hspeed : ContinuousOn (fun t => halfSpaceDensity n (δ t) * L t) (Icc a b)) :
    halfSpacePathDist (δ a) (δ b) ≤ ∫ t in a..b, halfSpaceDensity n (δ t) * L t := by
  let ρ := halfSpaceDensity n
  let β : ℝ → ℝ := IccExtend hab (fun t : Icc a b => ρ (δ t) * L t)
  have hβ : Continuous β := hspeed.domRestrict.Icc_extend'
  have hβeq (t : ℝ) (ht : t ∈ Icc a b) : β t = ρ (δ t) * L t :=
    IccExtend_of_mem hab _ ht
  have hg : ContinuousOn (fun t => halfSpacePathDist (δ a) (δ t)) (Icc a b) :=
    (ρ.continuous_pathDist_left (δ a)).comp_continuousOn hδ
  have hB : Continuous (fun t => ∫ s in a..t, β s) :=
    intervalIntegral.continuous_primitive (fun c d => hβ.intervalIntegrable c d) a
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary hg
    (B := fun t => ∫ s in a..t, β s) (B' := β) (by simp [halfSpacePathDist, Auxiliary.Analysis.Density.pathDist_self])
    hB.continuousOn
    (fun t _ => (hβ.integral_hasStrictDerivAt a t).hasDerivAt.hasDerivWithinAt)
    (fun t ht r hr => halfSpace_distance_right_slope_bound (hL t ht) (hslope t ht)
      ((hδ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds ht.2)] with s hs hsb
        exact ⟨ht.1.trans hs.le, hsb.le⟩))
      (δ a) (by simpa only [hβeq t ⟨ht.1, ht.2.le⟩] using hr))
  apply (hbound (right_mem_Icc.mpr hab)).trans_eq
  apply intervalIntegral.integral_congr
  intro t ht
  exact hβeq t (by simpa only [uIcc_of_le hab] using ht)

theorem halfSpaceHomeomorph_preservesSeparation {n : ℕ}
    (F : Inversive.ExtendedHomeomorph (n + 1))
    (hF : F '' poincareHalfSpaceSet n 1 = poincareHalfSpaceSet n 1)
    (hsep : PreservesPoincareSeparation F) (x y : HyperbolicHalfSpace n) :
    poincareSeparation (halfSpaceHomeomorph F hF x).val
      (halfSpaceHomeomorph F hF y).val = poincareSeparation x.val y.val := by
  obtain ⟨X, Y, _, _, hX, hY, hXY⟩ := hsep x.val y.val x.property y.property
  have heX : (halfSpaceHomeomorph F hF x).val = X := by
    apply OnePoint.coe_injective
    rw [halfSpaceHomeomorph_apply, hX]
  have heY : (halfSpaceHomeomorph F hF y).val = Y := by
    apply OnePoint.coe_injective
    rw [halfSpaceHomeomorph_apply, hY]
  rwa [heX, heY]

theorem poincareHalfSpaceHomeomorph_preservesSeparation {n : ℕ} [NeZero n]
    (g : Inversive.GM n) (x y : HyperbolicHalfSpace n) :
    poincareSeparation (poincareHalfSpaceHomeomorph g x).val
      (poincareHalfSpaceHomeomorph g y).val = poincareSeparation x.val y.val :=
  halfSpaceHomeomorph_preservesSeparation _ _ (poincareExtension_preservesSeparation g) x y

/-- The exact positive norm ratio determined by the separation invariant. -/
def halfSpaceSecantScale {n : ℕ} (f : HyperbolicHalfSpace n → HyperbolicHalfSpace n)
    (x y : HyperbolicHalfSpace n) : ℝ :=
  Real.sqrt (((f x).val (Fin.last n) * (f y).val (Fin.last n)) /
    (x.val (Fin.last n) * y.val (Fin.last n)))

theorem halfSpace_norm_sub_eq {n : ℕ} (f : HyperbolicHalfSpace n → HyperbolicHalfSpace n)
    (hsep : ∀ x y, poincareSeparation (f x).val (f y).val = poincareSeparation x.val y.val)
    (x y : HyperbolicHalfSpace n) :
    ‖(f x).val - (f y).val‖ = halfSpaceSecantScale f x y * ‖x.val - y.val‖ := by
  have hxy := hsep x y
  unfold poincareSeparation at hxy
  rw [dist_eq_norm, dist_eq_norm] at hxy
  have hpos : 0 < ((f x).val (Fin.last n) * (f y).val (Fin.last n)) /
      (x.val (Fin.last n) * y.val (Fin.last n)) :=
    div_pos (mul_pos (f x).property (f y).property) (mul_pos x.property y.property)
  have heq : ‖(f x).val - (f y).val‖ ^ 2 =
      (((f x).val (Fin.last n) * (f y).val (Fin.last n)) /
        (x.val (Fin.last n) * y.val (Fin.last n))) * ‖x.val - y.val‖ ^ 2 := by
    apply (div_eq_iff (mul_ne_zero (f x).property.ne' (f y).property.ne')).mp at hxy
    rw [hxy]
    ring
  calc
    ‖(f x).val - (f y).val‖ = Real.sqrt (‖(f x).val - (f y).val‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = halfSpaceSecantScale f x y * ‖x.val - y.val‖ := by
      rw [heq, Real.sqrt_mul hpos.le, Real.sqrt_sq (norm_nonneg _)]
      rfl

theorem halfSpace_normslope_eq {n : ℕ} (f : HyperbolicHalfSpace n → HyperbolicHalfSpace n)
    (hsep : ∀ x y, poincareSeparation (f x).val (f y).val = poincareSeparation x.val y.val)
    (γ : ℝ → HyperbolicHalfSpace n) (t s : ℝ) :
    ‖slope (fun u => (f (γ u)).val) t s‖ =
      halfSpaceSecantScale f (γ s) (γ t) * ‖slope (fun u => (γ u).val) t s‖ := by
  simp only [slope_def_module, norm_smul, Real.norm_eq_abs]
  rw [halfSpace_norm_sub_eq f hsep]
  ring

theorem halfSpace_normslope_tendsto {n : ℕ}
    (f : HyperbolicHalfSpace n → HyperbolicHalfSpace n) (hf : Continuous f)
    (hsep : ∀ x y, poincareSeparation (f x).val (f y).val = poincareSeparation x.val y.val)
    {γ : ℝ → HyperbolicHalfSpace n} {t : ℝ} {v : Inversive.Euclidean (n + 1)}
    (hγ : HasDerivWithinAt (fun u => (γ u).val) v (Ici t) t)
    (hγc : ContinuousWithinAt γ (Ioi t) t) :
    Tendsto (fun s => ‖slope (fun u => (f (γ u)).val) t s‖) (𝓝[>] t)
      (𝓝 (((f (γ t)).val (Fin.last n) / (γ t).val (Fin.last n)) * ‖v‖)) := by
  have hh : Tendsto (fun s => (γ s).val (Fin.last n)) (𝓝[>] t)
      (𝓝 ((γ t).val (Fin.last n))) :=
    (((halfSpaceHeight n).continuous.comp continuous_subtype_val).continuousAt.tendsto.comp hγc)
  have hhf : Tendsto (fun s => (f (γ s)).val (Fin.last n)) (𝓝[>] t)
      (𝓝 ((f (γ t)).val (Fin.last n))) :=
    (((halfSpaceHeight n).continuous.comp continuous_subtype_val).comp hf).continuousAt.tendsto.comp hγc
  have hc := ((hhf.mul (tendsto_const_nhds (x := (f (γ t)).val (Fin.last n)))).div
    (hh.mul (tendsto_const_nhds (x := (γ t).val (Fin.last n))))
    (mul_ne_zero (γ t).property.ne' (γ t).property.ne')).sqrt
  have hs := ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp hγ.Ioi_of_Ici).norm
  have heq : Real.sqrt (((f (γ t)).val (Fin.last n) * (f (γ t)).val (Fin.last n)) /
      ((γ t).val (Fin.last n) * (γ t).val (Fin.last n))) =
      (f (γ t)).val (Fin.last n) / (γ t).val (Fin.last n) := by
    rw [← div_mul_div_comm, ← sq, Real.sqrt_sq
      (div_pos (f (γ t)).property (γ t).property).le]
  rw [heq] at hc
  convert hc.mul hs using 1
  exact funext (fun s => halfSpace_normslope_eq f hsep γ t s)

/-- Separation covariance controls each mapped piece without assuming differentiability of the map. -/
theorem halfSpacePathDist_comp_piece_le {n : ℕ}
    (f : HyperbolicHalfSpace n → HyperbolicHalfSpace n) (hf : Continuous f)
    (hsep : ∀ x y, poincareSeparation (f x).val (f y).val = poincareSeparation x.val y.val)
    (γ : ℝ → HyperbolicHalfSpace n) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1 γ (Icc a b)) :
    halfSpacePathDist (f (γ a)) (f (γ b)) ≤ (halfSpacePieceLength γ a b).toReal := by
  let ρ := halfSpaceDensity n
  rcases hab.eq_or_lt with rfl | hab
  · simp [halfSpacePieceLength, Auxiliary.Analysis.Density.pieceLength,
      halfSpacePathDist, Auxiliary.Analysis.Density.pathDist_self]
  let δ := f ∘ γ
  let ν (t : ℝ) := derivWithin (fun u => (γ u).val) (Icc a b) t
  let L (t : ℝ) := ((f (γ t)).val (Fin.last n) / (γ t).val (Fin.last n)) * ‖ν t‖
  have hs (t : ℝ) : ρ (δ t) * L t = ρ (γ t) * ‖ν t‖ := by
    dsimp only [ρ, δ, Function.comp_def, L]
    rw [halfSpaceDensity_apply, halfSpaceDensity_apply]
    field_simp [(show 0 < (f (γ t)).val (Fin.last n) from (f (γ t)).property).ne',
      (show 0 < (γ t).val (Fin.last n) from (γ t).property).ne']
  have hc : ContinuousOn (fun t => ρ (γ t) * ‖ν t‖) (Icc a b) :=
    (ρ.continuous.comp_continuousOn hγ.continuousOn).mul
      ((Auxiliary.Analysis.openDomain_contDiffOn_ambient hγ).continuousOn_derivWithin
        (uniqueDiffOn_Icc hab) le_rfl).norm
  have hbound := halfSpacePathDist_le_integral_of_normslope δ L a b hab.le
    (hf.comp_continuousOn hγ.continuousOn)
    (fun t _ => mul_nonneg (div_pos (f (γ t)).property (γ t).property).le (norm_nonneg _))
    (fun t ht => halfSpace_normslope_tendsto f hf hsep
      (Auxiliary.Analysis.density_hasDerivWithinAt_right_of_Icc
        (((Auxiliary.Analysis.openDomain_contDiffOn_ambient hγ).differentiableOn one_ne_zero
          t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt) ht)
      ((hγ.continuousOn t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds ht.2)] with s hs hsb
        exact ⟨ht.1.trans hs.le, hsb.le⟩)))
    (hc.congr (fun t _ => hs t))
  have hint : (∫ t in a..b, ρ (δ t) * L t) = ∫ t in a..b, ρ (γ t) * ‖ν t‖ :=
    intervalIntegral.integral_congr (fun t _ => hs t)
  rw [hint] at hbound
  rw [halfSpacePieceLength, ρ.pieceLength_eq_ofReal_integral γ a b hab.le hγ,
    ENNReal.toReal_ofReal]
  · exact hbound
  · exact intervalIntegral.integral_nonneg hab.le (fun t _ =>
      mul_nonneg (ρ.positive (γ t)).le (norm_nonneg _))

theorem halfSpacePathDist_comp_chain_le {n : ℕ}
    (f : HyperbolicHalfSpace n → HyperbolicHalfSpace n) (hf : Continuous f)
    (hsep : ∀ x y, poincareSeparation (f x).val (f y).val = poincareSeparation x.val y.val)
    {x y : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) x y) :
    halfSpacePathDist (f x) (f y) ≤ (halfSpaceChainLength c).toReal := by
  let ρ := halfSpaceDensity n
  induction c with
  | nil x => simp [halfSpaceChainLength, Auxiliary.Analysis.Density.chainLength,
      halfSpacePathDist, Auxiliary.Analysis.Density.pathDist_self]
  | @cons x y z γ a b hab hc ha hb tail ih =>
      have hp := halfSpacePathDist_comp_piece_le f hf hsep γ a b hab hc
      rw [ha, hb] at hp
      calc
        halfSpacePathDist (f x) (f z) ≤
            halfSpacePathDist (f x) (f y) + halfSpacePathDist (f y) (f z) :=
          ρ.pathDist_triangle _ _ _
        _ ≤ (halfSpacePieceLength γ a b).toReal + (halfSpaceChainLength tail).toReal :=
          add_le_add hp ih
        _ = (halfSpaceChainLength (.cons γ a b hab hc ha hb tail)).toReal := by
          change (ρ.pieceLength γ a b).toReal + (ρ.chainLength tail).toReal =
            (ρ.pieceLength γ a b + ρ.chainLength tail).toReal
          exact (ENNReal.toReal_add (ρ.pieceLength_ne_top γ a b hab hc)
            (ρ.chainLength_ne_top tail)).symm

theorem halfSpacePathDist_comp_le {n : ℕ}
    (f : HyperbolicHalfSpace n → HyperbolicHalfSpace n) (hf : Continuous f)
    (hsep : ∀ x y, poincareSeparation (f x).val (f y).val = poincareSeparation x.val y.val)
    (x y : HyperbolicHalfSpace n) :
    halfSpacePathDist (f x) (f y) ≤ halfSpacePathDist x y := by
  let ρ := halfSpaceDensity n
  have he : ρ.pathEDist x y < ⊤ := (ρ.pathEDist_ne_top x y).lt_top
  rw [ρ.pathEDist_eq_piecewiseEDist, Auxiliary.Analysis.Density.piecewiseEDist, iInf_lt_iff] at he
  obtain ⟨c, _⟩ := he
  have hnonempty : (Set.range (fun d : Auxiliary.Analysis.RiemannianC1Chain
      𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) x y =>
      (halfSpaceChainLength d).toReal)).Nonempty := ⟨_, c, rfl⟩
  conv_rhs => rw [halfSpacePathDist_eq_sInf_chainLengths]
  apply le_csInf hnonempty
  rintro _ ⟨d, rfl⟩
  exact halfSpacePathDist_comp_chain_le f hf hsep d

/-- Every continuous separation-preserving homeomorphism is a genuine length-metric isometry. -/
theorem halfSpacePathDist_homeomorph {n : ℕ}
    (f : HyperbolicHalfSpace n ≃ₜ HyperbolicHalfSpace n)
    (hsep : ∀ x y, poincareSeparation (f x).val (f y).val = poincareSeparation x.val y.val)
    (x y : HyperbolicHalfSpace n) :
    halfSpacePathDist (f x) (f y) = halfSpacePathDist x y := by
  apply le_antisymm (halfSpacePathDist_comp_le f f.continuous hsep x y)
  have hinv : ∀ x y, poincareSeparation (f.symm x).val (f.symm y).val =
      poincareSeparation x.val y.val := by
    intro x y
    simpa only [f.apply_symm_apply] using (hsep (f.symm x) (f.symm y)).symm
  simpa only [f.symm_apply_apply] using
    halfSpacePathDist_comp_le f.symm f.symm.continuous hinv (f x) (f y)

/-- actual native Poincaré extensions preserve the genuine hyperbolic path metric. -/
theorem poincareHalfSpaceHomeomorph_pathDist {n : ℕ} [NeZero n]
    (g : Inversive.GM n) (x y : HyperbolicHalfSpace n) :
    halfSpacePathDist (poincareHalfSpaceHomeomorph g x) (poincareHalfSpaceHomeomorph g y) =
      halfSpacePathDist x y :=
  halfSpacePathDist_homeomorph _ (poincareHalfSpaceHomeomorph_preservesSeparation g) x y

/-- The isometry statement uses the proved hyperbolic metric, with no global metric-instance replacement. -/
theorem poincareHalfSpaceHomeomorph_isometry {n : ℕ} [NeZero n] (g : Inversive.GM n) :
    @Isometry (HyperbolicHalfSpace n) (HyperbolicHalfSpace n)
      (halfSpaceMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
      (halfSpaceMetricSpace n).toPseudoMetricSpace.toPseudoEMetricSpace
      (poincareHalfSpaceHomeomorph g) := by
  apply (@isometry_iff_dist_eq (HyperbolicHalfSpace n) (HyperbolicHalfSpace n)
    (halfSpaceMetricSpace n).toPseudoMetricSpace (halfSpaceMetricSpace n).toPseudoMetricSpace _).mpr
  intro x y
  simpa only [halfSpaceMetricSpace_dist] using poincareHalfSpaceHomeomorph_pathDist g x y


def halfSpaceLogHeight {n : ℕ} (x : HyperbolicHalfSpace n) : ℝ :=
  Real.log (x.val (Fin.last n))

theorem logHeight_dist_le_pieceLength {n : ℕ}
    (γ : ℝ → HyperbolicHalfSpace n) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1 γ (Icc a b)) :
    dist (halfSpaceLogHeight (γ a)) (halfSpaceLogHeight (γ b)) ≤
      (halfSpacePieceLength γ a b).toReal := by
  let ρ := halfSpaceDensity n
  let ν (t : ℝ) := derivWithin (fun u => (γ u).val) (Icc a b) t
  rcases hab.eq_or_lt with rfl | hab
  · simp [halfSpacePieceLength, Auxiliary.Analysis.Density.pieceLength]
  have hγa := Auxiliary.Analysis.openDomain_contDiffOn_ambient hγ
  have hlog (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt (fun u => halfSpaceLogHeight (γ u))
        ((halfSpaceHeight n (ν t)) / (γ t).val (Fin.last n)) t := by
    have hd := ((hγa.differentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩).hasDerivWithinAt).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
    exact ((halfSpaceHeight n).hasFDerivAt.comp_hasDerivAt t hd).log
      (show (γ t).val (Fin.last n) ≠ 0 from
        (show 0 < (γ t).val (Fin.last n) from (γ t).property).ne')
  have hc : ContinuousOn (fun t => ρ (γ t) * ‖ν t‖) (Icc a b) :=
    (ρ.continuous.comp_continuousOn hγ.continuousOn).mul
      (hγa.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl).norm
  have hcont : ContinuousOn (fun t => halfSpaceLogHeight (γ t)) (Icc a b) :=
    (((halfSpaceHeight n).continuous.comp continuous_subtype_val).comp_continuousOn
      hγ.continuousOn).log (fun t _ =>
        (show 0 < (γ t).val (Fin.last n) from (γ t).property).ne')
  have hdle (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖deriv (fun u => halfSpaceLogHeight (γ u)) t‖ ≤ ρ (γ t) * ‖ν t‖ := by
    rw [(hlog t ht).deriv]
    simp only [Real.norm_eq_abs, abs_div,
      abs_of_pos (show 0 < (γ t).val (Fin.last n) from (γ t).property)]
    change |(ν t) (Fin.last n)| / (γ t).val (Fin.last n) ≤ ρ (γ t) * ‖ν t‖
    have hn : |(ν t) (Fin.last n)| ≤ ‖ν t‖ := by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (ν t) (Fin.last n))
    calc
      _ ≤ ‖ν t‖ / (γ t).val (Fin.last n) :=
        div_le_div_of_nonneg_right hn (show 0 < (γ t).val (Fin.last n) from (γ t).property).le
      _ = _ := by rw [show ρ (γ t) = 1 / (γ t).val (Fin.last n) from rfl]; ring
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le hab.le hcont
    (fun t ht => (hlog t ht).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall hdle) (hc.intervalIntegrable_of_Icc hab.le)
  rw [halfSpacePieceLength, ρ.pieceLength_eq_ofReal_integral γ a b hab.le hγ,
    ENNReal.toReal_ofReal]
  · simpa only [dist_eq_norm, norm_sub_rev] using hbound
  · exact intervalIntegral.integral_nonneg hab.le (fun t _ =>
      mul_nonneg (ρ.positive (γ t)).le (norm_nonneg _))

theorem logHeight_dist_le_chainLength {n : ℕ} {x y : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) x y) :
    dist (halfSpaceLogHeight x) (halfSpaceLogHeight y) ≤ (halfSpaceChainLength c).toReal := by
  let ρ := halfSpaceDensity n
  induction c with
  | nil x => simp [halfSpaceChainLength, Auxiliary.Analysis.Density.chainLength]
  | @cons x y z γ a b hab hc ha hb tail ih =>
      have hp := logHeight_dist_le_pieceLength γ a b hab hc
      rw [ha, hb] at hp
      calc
        dist (halfSpaceLogHeight x) (halfSpaceLogHeight z) ≤
            dist (halfSpaceLogHeight x) (halfSpaceLogHeight y) +
              dist (halfSpaceLogHeight y) (halfSpaceLogHeight z) := dist_triangle _ _ _
        _ ≤ (halfSpacePieceLength γ a b).toReal + (halfSpaceChainLength tail).toReal :=
          add_le_add hp ih
        _ = (halfSpaceChainLength (.cons γ a b hab hc ha hb tail)).toReal := by
          change (ρ.pieceLength γ a b).toReal + (ρ.chainLength tail).toReal =
            (ρ.pieceLength γ a b + ρ.chainLength tail).toReal
          exact (ENNReal.toReal_add (ρ.pieceLength_ne_top γ a b hab hc)
            (ρ.chainLength_ne_top tail)).symm

theorem logHeight_dist_le_halfSpacePathDist {n : ℕ} (x y : HyperbolicHalfSpace n) :
    dist (halfSpaceLogHeight x) (halfSpaceLogHeight y) ≤ halfSpacePathDist x y := by
  let ρ := halfSpaceDensity n
  have he : ρ.pathEDist x y < ⊤ := (ρ.pathEDist_ne_top x y).lt_top
  rw [ρ.pathEDist_eq_piecewiseEDist, Auxiliary.Analysis.Density.piecewiseEDist, iInf_lt_iff] at he
  obtain ⟨c, _⟩ := he
  have hnonempty : (Set.range (fun d : Auxiliary.Analysis.RiemannianC1Chain
      𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) x y =>
      (halfSpaceChainLength d).toReal)).Nonempty := ⟨_, c, rfl⟩
  rw [halfSpacePathDist_eq_sInf_chainLengths]
  apply le_csInf hnonempty
  rintro _ ⟨d, rfl⟩
  exact logHeight_dist_le_chainLength d

/-- The unit vector normal to the Euclidean boundary. -/
def verticalUnitVector (n : ℕ) : Inversive.Euclidean (n + 1) := EuclideanSpace.single (Fin.last n) 1

theorem norm_verticalUnitVector (n : ℕ) : ‖verticalUnitVector n‖ = 1 := by
  simp [verticalUnitVector, EuclideanSpace.single, PiLp.norm_single]

/-- A genuine finite point on the positive vertical ray. -/
def verticalPoint (n : ℕ) (r : ℝ) (hr : 0 < r) : HyperbolicHalfSpace n :=
  ⟨r • verticalUnitVector n, by
    change 0 < (r • verticalUnitVector n) (Fin.last n)
    simpa [verticalUnitVector, PiLp.smul_apply] using hr⟩

theorem verticalPoint_height (n : ℕ) (r : ℝ) (hr : 0 < r) :
    (verticalPoint n r hr).val (Fin.last n) = r := by
  simp [verticalPoint, verticalUnitVector, PiLp.smul_apply]

/-- A global positive exponential parametrization, so no domain extension is concealed. -/
def verticalLogCurve (n : ℕ) (a b : ℝ) (t : ℝ) : HyperbolicHalfSpace n :=
  verticalPoint n (Real.exp ((1 - t) * a + t * b)) (Real.exp_pos _)

theorem contMDiff_verticalLogCurve (n : ℕ) (a b : ℝ) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1 (verticalLogCurve n a b) := by
  have ha : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (fun t : ℝ => (1 - t) * a + t * b) :=
    ((contDiff_const.sub contDiff_id).mul contDiff_const).add (contDiff_id.mul contDiff_const)
  have h : ContDiff ℝ ((⊤ : ℕ∞) : ℕ∞ω) (fun t : ℝ => (verticalLogCurve n a b t).val) :=
    ha.exp.smul contDiff_const
  exact ((ContMDiff.subtypeVal_comp_iff (upperHalfSpaceDomain n)
    (verticalLogCurve n a b)).mp h.contMDiff).of_le (by norm_num)

theorem verticalLogCurve_hasDerivAt (n : ℕ) (a b t : ℝ) :
    HasDerivAt (fun u => (verticalLogCurve n a b u).val)
      ((Real.exp ((1 - t) * a + t * b) * (b - a)) • verticalUnitVector n) t := by
  have h : HasDerivAt (fun u : ℝ => (1 - u) * a + u * b) (b - a) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const a).add
      ((hasDerivAt_id t).mul_const b) using 1 <;>
      (first | rfl | ring)
  exact h.exp.smul_const (verticalUnitVector n)

theorem verticalLogCurve_endpoints (n : ℕ) (a b : ℝ) :
    verticalLogCurve n a b 0 = verticalPoint n (Real.exp a) (Real.exp_pos a) ∧
    verticalLogCurve n a b 1 = verticalPoint n (Real.exp b) (Real.exp_pos b) := by
  constructor <;> apply Subtype.ext <;> simp [verticalLogCurve, verticalPoint]

theorem verticalLogCurve_pieceLength (n : ℕ) (a b : ℝ) :
    halfSpacePieceLength (verticalLogCurve n a b) 0 1 = ENNReal.ofReal |b - a| := by
  rw [halfSpacePieceLength_eq_coordinate_integral _ _ _ zero_le_one
    (contMDiff_verticalLogCurve n a b).contMDiffOn]
  have heq (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      ‖derivWithin (fun u => (verticalLogCurve n a b u).val) (Icc (0 : ℝ) 1) t‖ /
        (verticalLogCurve n a b t).val (Fin.last n) = |b - a| := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    rw [(verticalLogCurve_hasDerivAt n a b t).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one t ht'), norm_smul, norm_verticalUnitVector, mul_one,
      Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [verticalLogCurve, verticalPoint_height]
    exact mul_div_cancel_left₀ |b - a| (Real.exp_ne_zero _)
  rw [intervalIntegral.integral_congr heq]
  simp

theorem verticalPoint_exp_pathDist (n : ℕ) (a b : ℝ) :
    halfSpacePathDist (verticalPoint n (Real.exp a) (Real.exp_pos a))
      (verticalPoint n (Real.exp b) (Real.exp_pos b)) = |b - a| := by
  have hlow := logHeight_dist_le_halfSpacePathDist
    (verticalPoint n (Real.exp a) (Real.exp_pos a))
    (verticalPoint n (Real.exp b) (Real.exp_pos b))
  have hupp := halfSpacePathDist_comp_piece_le (fun x : HyperbolicHalfSpace n => x)
    continuous_id (fun _ _ => rfl) (verticalLogCurve n a b) 0 1 zero_le_one
    (contMDiff_verticalLogCurve n a b).contMDiffOn
  rw [(verticalLogCurve_endpoints n a b).1, (verticalLogCurve_endpoints n a b).2,
    verticalLogCurve_pieceLength, ENNReal.toReal_ofReal (abs_nonneg _)] at hupp
  apply le_antisymm hupp
  simpa only [halfSpaceLogHeight, verticalPoint_height, Real.log_exp,
    Real.dist_eq, abs_sub_comm] using hlow

/-- exact distance along the positive vertical ray. -/
theorem verticalPoint_pathDist (n : ℕ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    halfSpacePathDist (verticalPoint n s hs) (verticalPoint n t ht) = |Real.log (s / t)| := by
  have h := verticalPoint_exp_pathDist n (Real.log s) (Real.log t)
  simpa only [Real.exp_log hs, Real.exp_log ht, Real.log_div hs.ne' ht.ne', abs_sub_comm]
    using h


section TwoPlane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The linear inclusion of the plane spanned by two chosen vectors. -/
def twoPlaneEmbedCLM (u e : E) : ℂ →L[ℝ] E :=
  Complex.reCLM.smulRight u + Complex.imCLM.smulRight e

theorem twoPlaneEmbedCLM_apply (u e : E) (z : ℂ) :
    twoPlaneEmbedCLM u e z = z.re • u + z.im • e := rfl

/-- Coordinates along two chosen real vectors, represented as a complex number. -/
def twoPlaneProjectCLM (u e : E) : E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ u) +
    Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ e))

theorem twoPlaneProjectCLM_re (u e v : E) :
    (twoPlaneProjectCLM u e v).re = ⟪u, v⟫_ℝ := by
  simp [twoPlaneProjectCLM]

theorem twoPlaneProjectCLM_im (u e v : E) :
    (twoPlaneProjectCLM u e v).im = ⟪e, v⟫_ℝ := by
  simp [twoPlaneProjectCLM]

theorem twoPlaneEmbedCLM_norm (u e : E) (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (hue : ⟪u, e⟫_ℝ = 0) (z : ℂ) : ‖twoPlaneEmbedCLM u e z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have horth : ⟪z.re • u, z.im • e⟫_ℝ = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, hue]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (𝕜 := ℝ) (z.re • u) (z.im • e) horth
  rw [twoPlaneEmbedCLM_apply]
  simp only [norm_smul, hu, he, mul_one, Real.norm_eq_abs] at hp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  nlinarith [sq_abs z.re, sq_abs z.im]

theorem twoPlaneProjectCLM_embed (u e : E) (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (hue : ⟪u, e⟫_ℝ = 0) (z : ℂ) :
    twoPlaneProjectCLM u e (twoPlaneEmbedCLM u e z) = z := by
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm, hue]
  apply Complex.ext
  · simp [twoPlaneProjectCLM_re, twoPlaneEmbedCLM_apply, hu, hue]
  · simp [twoPlaneProjectCLM_im, twoPlaneEmbedCLM_apply, he, heu]

theorem twoPlaneProjectCLM_norm_le (u e : E) (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (hue : ⟪u, e⟫_ℝ = 0) (v : E) : ‖twoPlaneProjectCLM u e v‖ ≤ ‖v‖ := by
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm, hue]
  have h := real_inner_self_nonneg (x := v - ⟪u, v⟫_ℝ • u - ⟪e, v⟫_ℝ • e)
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hue, heu, real_inner_self_eq_norm_sq,
    norm_smul, hu, he, mul_one, Real.norm_eq_abs, sq_abs] at h
  have huv : ⟪v, u⟫_ℝ = ⟪u, v⟫_ℝ := real_inner_comm _ _
  have hev : ⟪v, e⟫_ℝ = ⟪e, v⟫_ℝ := real_inner_comm _ _
  rw [huv, hev] at h
  have hsq : ‖twoPlaneProjectCLM u e v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      twoPlaneProjectCLM_re, twoPlaneProjectCLM_im]
    nlinarith
  nlinarith [norm_nonneg (twoPlaneProjectCLM u e v), norm_nonneg v]

end TwoPlane

/-- The upward unit vector in the Euclidean upper-half-space coordinates. -/
def halfSpaceVerticalUnit (n : ℕ) : Inversive.Euclidean (n + 1) :=
  EuclideanSpace.single (Fin.last n) 1

theorem halfSpaceVerticalUnit_norm (n : ℕ) : ‖halfSpaceVerticalUnit n‖ = 1 := by
  simp [halfSpaceVerticalUnit, PiLp.norm_single]

theorem halfSpaceHeight_verticalUnit (n : ℕ) :
    halfSpaceHeight n (halfSpaceVerticalUnit n) = 1 := by
  simp [halfSpaceHeight, halfSpaceVerticalUnit]

theorem halfSpaceVerticalUnit_inner (n : ℕ) (v : Inversive.Euclidean (n + 1)) :
    ⟪halfSpaceVerticalUnit n, v⟫_ℝ = halfSpaceHeight n v := by
  simp [halfSpaceVerticalUnit, EuclideanSpace.inner_single_left, halfSpaceHeight]

theorem inner_halfSpaceVerticalUnit (n : ℕ) (v : Inversive.Euclidean (n + 1)) :
    ⟪v, halfSpaceVerticalUnit n⟫_ℝ = halfSpaceHeight n v := by
  rw [real_inner_comm, halfSpaceVerticalUnit_inner]

/-- The horizontal part of a Euclidean vector. -/
def halfSpaceHorizontalPart {n : ℕ} (v : Inversive.Euclidean (n + 1)) : Inversive.Euclidean (n + 1) :=
  v - halfSpaceHeight n v • halfSpaceVerticalUnit n

theorem halfSpaceHeight_horizontalPart {n : ℕ} (v : Inversive.Euclidean (n + 1)) :
    halfSpaceHeight n (halfSpaceHorizontalPart v) = 0 := by
  simp [halfSpaceHorizontalPart, halfSpaceHeight_verticalUnit]

/-- The linear part of a vertical-plane embedding. -/
def halfSpacePlaneEmbedCLM {n : ℕ} (u : Inversive.Euclidean (n + 1)) : ℂ →L[ℝ] Inversive.Euclidean (n + 1) :=
  twoPlaneEmbedCLM u (halfSpaceVerticalUnit n)

/-- The linear part of the orthogonal vertical-plane projection. -/
def halfSpacePlaneProjectCLM {n : ℕ} (u : Inversive.Euclidean (n + 1)) : Inversive.Euclidean (n + 1) →L[ℝ] ℂ :=
  twoPlaneProjectCLM u (halfSpaceVerticalUnit n)

theorem halfSpacePlaneEmbedCLM_norm {n : ℕ} (u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (z : ℂ) :
    ‖halfSpacePlaneEmbedCLM u z‖ = ‖z‖ :=
  twoPlaneEmbedCLM_norm u _ hu (halfSpaceVerticalUnit_norm n)
    (by rw [inner_halfSpaceVerticalUnit, hu0]) z

theorem halfSpacePlaneProjectCLM_norm_le {n : ℕ} (u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (v : Inversive.Euclidean (n + 1)) :
    ‖halfSpacePlaneProjectCLM u v‖ ≤ ‖v‖ :=
  twoPlaneProjectCLM_norm_le u _ hu (halfSpaceVerticalUnit_norm n)
    (by rw [inner_halfSpaceVerticalUnit, hu0]) v

theorem halfSpacePlaneEmbedCLM_height {n : ℕ} (u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) (z : ℂ) :
    halfSpaceHeight n (halfSpacePlaneEmbedCLM u z) = z.im := by
  simp [halfSpacePlaneEmbedCLM, twoPlaneEmbedCLM_apply, hu0, halfSpaceHeight_verticalUnit]

theorem halfSpacePlaneProjectCLM_im {n : ℕ} (u v : Inversive.Euclidean (n + 1)) :
    (halfSpacePlaneProjectCLM u v).im = halfSpaceHeight n v := by
  rw [halfSpacePlaneProjectCLM, twoPlaneProjectCLM_im, halfSpaceVerticalUnit_inner]

theorem halfSpacePlaneProjectCLM_embed {n : ℕ} (u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (z : ℂ) :
    halfSpacePlaneProjectCLM u (halfSpacePlaneEmbedCLM u z) = z :=
  twoPlaneProjectCLM_embed u _ hu (halfSpaceVerticalUnit_norm n)
    (by rw [inner_halfSpaceVerticalUnit, hu0]) z

/-- The affine vertical plane through the horizontal part of the chosen base point. -/
def halfSpacePlaneEmbed {n : ℕ} (x u : Inversive.Euclidean (n + 1)) (z : ℂ) : Inversive.Euclidean (n + 1) :=
  halfSpaceHorizontalPart x + halfSpacePlaneEmbedCLM u z

/-- Orthogonal projection onto a vertical plane, retaining the absolute height. -/
def halfSpacePlaneProject {n : ℕ} (x u v : Inversive.Euclidean (n + 1)) : ℂ :=
  halfSpacePlaneProjectCLM u (v - halfSpaceHorizontalPart x)

theorem halfSpacePlaneEmbed_height {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) (z : ℂ) :
    halfSpaceHeight n (halfSpacePlaneEmbed x u z) = z.im := by
  simp [halfSpacePlaneEmbed, halfSpaceHeight_horizontalPart, halfSpacePlaneEmbedCLM_height, hu0]

theorem halfSpacePlaneProject_im {n : ℕ} (x u v : Inversive.Euclidean (n + 1)) :
    (halfSpacePlaneProject x u v).im = halfSpaceHeight n v := by
  simp [halfSpacePlaneProject, halfSpacePlaneProjectCLM_im, halfSpaceHeight_horizontalPart]

theorem halfSpacePlaneProject_re {n : ℕ} (x u v : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) :
    (halfSpacePlaneProject x u v).re = ⟪v - x, u⟫_ℝ := by
  rw [halfSpacePlaneProject, halfSpacePlaneProjectCLM, twoPlaneProjectCLM_re]
  simp only [halfSpaceHorizontalPart, inner_sub_right, real_inner_smul_right,
    inner_halfSpaceVerticalUnit, hu0, mul_zero, sub_zero]
  rw [inner_sub_left, real_inner_comm u v, real_inner_comm u x]

theorem halfSpacePlaneProject_embed {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (z : ℂ) :
    halfSpacePlaneProject x u (halfSpacePlaneEmbed x u z) = z := by
  simpa [halfSpacePlaneProject, halfSpacePlaneEmbed] using halfSpacePlaneProjectCLM_embed u hu hu0 z

theorem halfSpacePlaneEmbed_hasFDerivAt {n : ℕ} (x u : Inversive.Euclidean (n + 1)) (z : ℂ) :
    HasFDerivAt (halfSpacePlaneEmbed x u) (halfSpacePlaneEmbedCLM u) z :=
  (halfSpacePlaneEmbedCLM u).hasFDerivAt.const_add _

theorem halfSpacePlaneProject_hasFDerivAt {n : ℕ} (x u v : Inversive.Euclidean (n + 1)) :
    HasFDerivAt (halfSpacePlaneProject x u) (halfSpacePlaneProjectCLM u) v := by
  have h : HasFDerivAt
      (fun w : Inversive.Euclidean (n + 1) => halfSpacePlaneProjectCLM u w -
        halfSpacePlaneProjectCLM u (halfSpaceHorizontalPart x))
      (halfSpacePlaneProjectCLM u) v :=
    (halfSpacePlaneProjectCLM u).hasFDerivAt.sub_const _
  convert h using 1
  funext w
  exact map_sub _ _ _

theorem halfSpacePlaneEmbed_dist {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (z w : ℂ) :
    dist (halfSpacePlaneEmbed x u z) (halfSpacePlaneEmbed x u w) = dist z w := by
  simp only [dist_eq_norm, halfSpacePlaneEmbed, add_sub_add_left_eq_sub,
    ← map_sub, halfSpacePlaneEmbedCLM_norm u hu hu0]

theorem halfSpacePlaneProject_dist_le {n : ℕ} (x u v w : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) :
    dist (halfSpacePlaneProject x u v) (halfSpacePlaneProject x u w) ≤ dist v w := by
  simpa [dist_eq_norm, halfSpacePlaneProject, ← map_sub] using
    halfSpacePlaneProjectCLM_norm_le u hu hu0 (v - w)

theorem halfSpacePlaneEmbed_base {n : ℕ} (x u : Inversive.Euclidean (n + 1)) :
    halfSpacePlaneEmbed x u ((halfSpaceHeight n x : ℂ) * Complex.I) = x := by
  simp [halfSpacePlaneEmbed, halfSpacePlaneEmbedCLM, twoPlaneEmbedCLM_apply,
    halfSpaceHorizontalPart]

theorem halfSpacePlaneEmbed_of_horizontalPart_sub {n : ℕ}
    (x y u : Inversive.Euclidean (n + 1)) (t : ℝ)
    (hxy : halfSpaceHorizontalPart (y - x) = t • u) :
    halfSpacePlaneEmbed x u ((t : ℂ) + (halfSpaceHeight n y : ℂ) * Complex.I) = y := by
  have h := hxy
  simp only [halfSpaceHorizontalPart, map_sub] at h
  simp only [halfSpacePlaneEmbed, halfSpacePlaneEmbedCLM, twoPlaneEmbedCLM_apply,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, sub_self, add_zero, Complex.add_im,
    Complex.mul_im, mul_one]
  rw [← h]
  dsimp [halfSpaceHorizontalPart]
  module

theorem exists_halfSpace_horizontal_direction {n : ℕ} (hn : 1 ≤ n)
    (x y : Inversive.Euclidean (n + 1)) :
    ∃ u : Inversive.Euclidean (n + 1), ∃ t : ℝ,
      ‖u‖ = 1 ∧ halfSpaceHeight n u = 0 ∧ halfSpaceHorizontalPart (y - x) = t • u := by
  by_cases hxy : halfSpaceHorizontalPart (y - x) = 0
  · refine ⟨EuclideanSpace.single (0 : Fin (n + 1)) 1, 0, ?_, ?_, ?_⟩
    · simp [PiLp.norm_single]
    · have hne : (Fin.last n : Fin (n + 1)) ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_zero] at this
        omega
      simp [halfSpaceHeight, hne]
    · simpa using hxy
  · refine ⟨normalize (halfSpaceHorizontalPart (y - x)),
      ‖halfSpaceHorizontalPart (y - x)‖, norm_normalize hxy, ?_, ?_⟩
    · simp [NormedSpace.normalize, halfSpaceHeight_horizontalPart]
    · exact (norm_smul_normalize _).symm

theorem exists_halfSpace_plane_through_pair {n : ℕ} (hn : 1 ≤ n)
    (x y : Inversive.Euclidean (n + 1)) :
    ∃ u : Inversive.Euclidean (n + 1), ∃ t : ℝ, ‖u‖ = 1 ∧ halfSpaceHeight n u = 0 ∧
      halfSpacePlaneEmbed x u ((halfSpaceHeight n x : ℂ) * Complex.I) = x ∧
      halfSpacePlaneEmbed x u ((t : ℂ) + (halfSpaceHeight n y : ℂ) * Complex.I) = y := by
  obtain ⟨u, t, hu, hu0, hxy⟩ := exists_halfSpace_horizontal_direction hn x y
  exact ⟨u, t, hu, hu0, halfSpacePlaneEmbed_base x u,
    halfSpacePlaneEmbed_of_horizontalPart_sub x y u t hxy⟩


/-! ## Vertical-plane curve comparison -/

open scoped UpperHalfPlane Topology ContDiff ENNReal

/-- The vertical-plane projection maps positive height to the actual upper half-plane. -/
def halfSpacePlaneProjectUHP {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (p : HyperbolicHalfSpace n) : ℍ :=
  ⟨halfSpacePlaneProject x u p.val, by rw [halfSpacePlaneProject_im]; exact p.property⟩

/-- A horizontal direction gives an inclusion of the actual upper half-plane. -/
def halfSpacePlaneEmbedUHP {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) (z : ℍ) : HyperbolicHalfSpace n :=
  ⟨halfSpacePlaneEmbed x u z, by rw [mem_upperHalfSpaceDomain,
    halfSpacePlaneEmbed_height x u hu0]; exact z.im_pos⟩

theorem halfSpacePlaneProjectUHP_im {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (p : HyperbolicHalfSpace n) :
    (halfSpacePlaneProjectUHP x u p).im = halfSpaceHeight n p.val :=
  halfSpacePlaneProject_im x u p.val

theorem halfSpacePlaneProjectUHP_continuous {n : ℕ} (x u : Inversive.Euclidean (n + 1)) :
    Continuous (halfSpacePlaneProjectUHP x u) := by
  apply Continuous.upperHalfPlaneMk
  exact (continuous_iff_continuousAt.mpr
    (fun v => (halfSpacePlaneProject_hasFDerivAt x u v).continuousAt)).comp
    continuous_subtype_val

theorem halfSpacePlaneEmbedUHP_continuous {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) : Continuous (halfSpacePlaneEmbedUHP x u hu0) := by
  apply Continuous.subtype_mk
  exact (continuous_iff_continuousAt.mpr
    (fun z => (halfSpacePlaneEmbed_hasFDerivAt x u z).continuousAt)).comp
    UpperHalfPlane.continuous_coe

theorem halfSpacePlaneProjectUHP_embed {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (z : ℍ) :
    halfSpacePlaneProjectUHP x u (halfSpacePlaneEmbedUHP x u hu0 z) = z := by
  apply UpperHalfPlane.ext
  exact halfSpacePlaneProject_embed x u hu hu0 z

/-- Projecting a C1 coordinate curve produces an actual C1 upper-half-plane piece. -/
def halfSpacePlaneProjectPiece {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (γ : ℝ → HyperbolicHalfSpace n) (ν : ℝ → Inversive.Euclidean (n + 1))
    (a b : ℝ) (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hν : ContinuousOn ν (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => (γ s).val) (ν t) (Icc a b) t) :
    C1CurvePiece where
  a := a
  b := b
  ordered := hab
  curve := halfSpacePlaneProjectUHP x u ∘ γ
  velocity := halfSpacePlaneProjectCLM u ∘ ν
  continuous_curve := (halfSpacePlaneProjectUHP_continuous x u).comp_continuousOn hγ
  continuous_velocity := (halfSpacePlaneProjectCLM u).continuous.comp_continuousOn hν
  hasDerivWithin t ht := by
    have hf : HasFDerivAt (halfSpacePlaneProject x u) (halfSpacePlaneProjectCLM u) (γ t).val :=
      halfSpacePlaneProject_hasFDerivAt x u (γ t).val
    have h : HasDerivWithinAt (halfSpacePlaneProject x u ∘ fun s => (γ s).val)
        (halfSpacePlaneProjectCLM u (ν t)) (Icc a b) t :=
      hf.comp_hasDerivWithinAt t (hd t ht)
    exact h

theorem halfSpacePlaneProject_piece_dist_le_integral {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (γ : ℝ → HyperbolicHalfSpace n) (ν : ℝ → Inversive.Euclidean (n + 1))
    (a b : ℝ) (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hν : ContinuousOn ν (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => (γ s).val) (ν t) (Icc a b) t) :
    dist (halfSpacePlaneProjectUHP x u (γ a)) (halfSpacePlaneProjectUHP x u (γ b)) ≤
      ∫ t in a..b, ‖ν t‖ / halfSpaceHeight n (γ t).val := by
  let c := halfSpacePlaneProjectPiece x u γ ν a b hab hγ hν hd
  apply c.dist_le_length.trans
  apply intervalIntegral.integral_mono_on hab (c.continuous_speed.intervalIntegrable_of_Icc hab)
    ((hν.norm.div ((halfSpaceHeight n).continuous.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn hγ))
      (fun t _ => (show 0 < halfSpaceHeight n (γ t).val from (γ t).property).ne')).intervalIntegrable_of_Icc hab)
  intro t _
  change ‖halfSpacePlaneProjectCLM u (ν t)‖ /
    (halfSpacePlaneProjectUHP x u (γ t)).im ≤ _
  rw [halfSpacePlaneProjectUHP_im]
  exact div_le_div_of_nonneg_right (halfSpacePlaneProjectCLM_norm_le u hu hu0 (ν t))
    (show 0 ≤ halfSpaceHeight n (γ t).val from (γ t).property.le)

theorem halfSpacePlaneProject_piece_dist_le {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (γ : ℝ → HyperbolicHalfSpace n) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1 γ (Icc a b)) :
    dist (halfSpacePlaneProjectUHP x u (γ a)) (halfSpacePlaneProjectUHP x u (γ b)) ≤
      (halfSpacePieceLength γ a b).toReal := by
  rw [halfSpacePieceLength_eq_coordinate_integral γ a b hab hγ, ENNReal.toReal_ofReal]
  · rcases hab.eq_or_lt with rfl | hab
    · simp
    exact halfSpacePlaneProject_piece_dist_le_integral x u hu hu0 γ _ a b hab.le hγ.continuousOn
      ((Auxiliary.Analysis.openDomain_contDiffOn_ambient hγ).continuousOn_derivWithin
        (uniqueDiffOn_Icc hab) le_rfl)
      (fun t ht => ((Auxiliary.Analysis.openDomain_contDiffOn_ambient hγ).differentiableOn
        one_ne_zero t ht).hasDerivWithinAt)
  · exact intervalIntegral.integral_nonneg hab (fun t _ => div_nonneg (norm_nonneg _)
      (show 0 ≤ (γ t).val (Fin.last n) from (γ t).property.le))

theorem halfSpacePlaneProject_chain_dist_le {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    {p q : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q) :
    dist (halfSpacePlaneProjectUHP x u p) (halfSpacePlaneProjectUHP x u q) ≤
      (halfSpaceChainLength c).toReal := by
  induction c with
  | nil p => simp [halfSpaceChainLength, Auxiliary.Analysis.Density.chainLength]
  | cons γ a b hab hc ha hb tail ih =>
    have hp := halfSpacePlaneProject_piece_dist_le x u hu hu0 γ a b hab hc
    rw [ha, hb] at hp
    calc
      _ ≤ dist (halfSpacePlaneProjectUHP x u _) (halfSpacePlaneProjectUHP x u _) +
          dist (halfSpacePlaneProjectUHP x u _) (halfSpacePlaneProjectUHP x u _) :=
        dist_triangle _ _ _
      _ ≤ (halfSpacePieceLength γ a b).toReal + (halfSpaceChainLength tail).toReal :=
        add_le_add hp ih
      _ = _ := by
        simp only [halfSpaceChainLength, Auxiliary.Analysis.Density.chainLength, halfSpacePieceLength,
          ENNReal.toReal_add ((halfSpaceDensity n).pieceLength_ne_top γ a b hab hc)
            ((halfSpaceDensity n).chainLength_ne_top tail)]

/-- Projection decreases the genuine length-infimum distance. -/
theorem halfSpacePlaneProject_dist_le_pathDist {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (p q : HyperbolicHalfSpace n) :
    dist (halfSpacePlaneProjectUHP x u p) (halfSpacePlaneProjectUHP x u q) ≤
      halfSpacePathDist p q := by
  have h : ENNReal.ofReal
      (dist (halfSpacePlaneProjectUHP x u p) (halfSpacePlaneProjectUHP x u q)) ≤
      halfSpacePathEDist p q := by
    rw [halfSpacePathEDist_eq_iInf_chainLengths]
    apply le_iInf
    intro c
    exact (ENNReal.ofReal_le_iff_le_toReal ((halfSpaceDensity n).chainLength_ne_top c)).mpr
      (halfSpacePlaneProject_chain_dist_le x u hu hu0 c)
  simpa only [halfSpacePathDist, Auxiliary.Analysis.Density.pathDist, halfSpacePathEDist,
    ENNReal.toReal_ofReal dist_nonneg] using
    ENNReal.toReal_mono (halfSpacePathEDist_ne_top p q) h

/-- An embedded C1 upper-half-plane piece has the same speed integral in the ambient half-space. -/
theorem halfSpacePlaneEmbed_piece_pathDist_le {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (c : C1CurvePiece) :
    halfSpacePathDist (halfSpacePlaneEmbedUHP x u hu0 (c.curve c.a))
      (halfSpacePlaneEmbedUHP x u hu0 (c.curve c.b)) ≤ c.length := by
  let δ := halfSpacePlaneEmbedUHP x u hu0 ∘ c.curve
  let ν := halfSpacePlaneEmbedCLM u ∘ c.velocity
  have hs (t : ℝ) : halfSpaceDensity n (δ t) * ‖ν t‖ =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.weightedSpeed c.curve c.velocity t := by
    dsimp only [δ, ν, Function.comp_def, halfSpacePlaneEmbedUHP]
    rw [halfSpaceDensity_apply, ← halfSpaceHeight_apply,
      halfSpacePlaneEmbed_height x u hu0, halfSpacePlaneEmbedCLM_norm u hu hu0]
    dsimp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.weightedSpeed]
    ring
  have hbound := (halfSpaceDensity n).pathDist_le_integral_of_continuous_speed δ ν
    c.a c.b c.ordered
    ((halfSpacePlaneEmbedUHP_continuous x u hu0).comp_continuousOn c.continuous_curve)
    (fun t ht => by
      have hf : HasFDerivAt (halfSpacePlaneEmbed x u) (halfSpacePlaneEmbedCLM u) (c.curve t : ℂ) :=
        halfSpacePlaneEmbed_hasFDerivAt x u (c.curve t : ℂ)
      have h : HasDerivWithinAt (halfSpacePlaneEmbed x u ∘ fun s => (c.curve s : ℂ))
          (halfSpacePlaneEmbedCLM u (c.velocity t)) (Icc c.a c.b) t :=
        hf.comp_hasDerivWithinAt t (c.hasDerivWithin t ht)
      exact h)
    (c.continuous_speed.congr (fun t _ => hs t))
  change halfSpacePathDist (δ c.a) (δ c.b) ≤ _
  exact hbound.trans_eq (intervalIntegral.integral_congr (fun t _ => hs t))

theorem halfSpacePlaneEmbed_pathDist_le {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (z w : ℍ) :
    halfSpacePathDist (halfSpacePlaneEmbedUHP x u hu0 z)
      (halfSpacePlaneEmbedUHP x u hu0 w) ≤ dist z w := by
  obtain ⟨c, rfl, rfl, hlen⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_length_minimizing_piece z w
  exact (halfSpacePlaneEmbed_piece_pathDist_le x u hu hu0 c).trans_eq hlen

/-- The actual ambient length metric restricts to the actual hyperbolic-plane metric. -/
theorem halfSpacePlaneEmbed_pathDist {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (z w : ℍ) :
    halfSpacePathDist (halfSpacePlaneEmbedUHP x u hu0 z)
      (halfSpacePlaneEmbedUHP x u hu0 w) = dist z w := by
  apply le_antisymm (halfSpacePlaneEmbed_pathDist_le x u hu hu0 z w)
  simpa only [halfSpacePlaneProjectUHP_embed x u hu hu0] using
    halfSpacePlaneProject_dist_le_pathDist x u hu hu0
      (halfSpacePlaneEmbedUHP x u hu0 z) (halfSpacePlaneEmbedUHP x u hu0 w)

/-- Every pair in dimension at least two lies in one embedded upper half-plane. -/
theorem exists_halfSpacePlaneEmbedUHP_pair {n : ℕ} (hn : 1 ≤ n)
    (p q : HyperbolicHalfSpace n) :
    ∃ (u : Inversive.Euclidean (n + 1)) (hu0 : halfSpaceHeight n u = 0), ‖u‖ = 1 ∧
      ∃ z w : ℍ, halfSpacePlaneEmbedUHP p.val u hu0 z = p ∧
        halfSpacePlaneEmbedUHP p.val u hu0 w = q := by
  obtain ⟨u, t, hu, hu0, hp, hq⟩ := exists_halfSpace_plane_through_pair hn p.val q.val
  let z : ℍ := ⟨(halfSpaceHeight n p.val : ℂ) * Complex.I, by
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, zero_mul, add_zero] using
      (show 0 < halfSpaceHeight n p.val from p.property)⟩
  let w : ℍ := ⟨(t : ℂ) + (halfSpaceHeight n q.val : ℂ) * Complex.I, by
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] using
      (show 0 < halfSpaceHeight n q.val from q.property)⟩
  exact ⟨u, hu0, hu, z, w, Subtype.ext hp, Subtype.ext hq⟩

/-- The cosh formula for the genuine upper-half-space length metric in every dimension ≥ 2. -/
theorem halfSpacePathDist_cosh {n : ℕ} (hn : 1 ≤ n) (p q : HyperbolicHalfSpace n) :
    Real.cosh (halfSpacePathDist p q) =
      1 + ‖p.val - q.val‖ ^ 2 / (2 * halfSpaceHeight n p.val * halfSpaceHeight n q.val) := by
  obtain ⟨u, hu0, hu, z, w, hp, hq⟩ := exists_halfSpacePlaneEmbedUHP_pair hn p q
  have hdist := halfSpacePlaneEmbed_pathDist p.val u hu hu0 z w
  rw [hp, hq] at hdist
  have hnorm := halfSpacePlaneEmbed_dist p.val u hu hu0 (z : ℂ) (w : ℂ)
  change dist (halfSpacePlaneEmbedUHP p.val u hu0 z).val
    (halfSpacePlaneEmbedUHP p.val u hu0 w).val = dist (z : ℂ) (w : ℂ) at hnorm
  rw [hp, hq, dist_eq_norm] at hnorm
  have hz := halfSpacePlaneEmbed_height p.val u hu0 (z : ℂ)
  have hw := halfSpacePlaneEmbed_height p.val u hu0 (w : ℂ)
  change halfSpaceHeight n (halfSpacePlaneEmbedUHP p.val u hu0 z).val = z.im at hz
  change halfSpaceHeight n (halfSpacePlaneEmbedUHP p.val u hu0 w).val = w.im at hw
  rw [hp] at hz
  rw [hq] at hw
  rw [hdist, UpperHalfPlane.cosh_dist, ← hnorm, ← hz, ← hw]

theorem halfSpacePathDist_eq_arsinh {n : ℕ} (hn : 1 ≤ n) (p q : HyperbolicHalfSpace n) :
    halfSpacePathDist p q = 2 * Real.arsinh (‖p.val - q.val‖ /
      (2 * Real.sqrt (halfSpaceHeight n p.val * halfSpaceHeight n q.val))) := by
  obtain ⟨u, hu0, hu, z, w, hp, hq⟩ := exists_halfSpacePlaneEmbedUHP_pair hn p q
  have hdist := halfSpacePlaneEmbed_pathDist p.val u hu hu0 z w
  rw [hp, hq] at hdist
  have hnorm := halfSpacePlaneEmbed_dist p.val u hu hu0 (z : ℂ) (w : ℂ)
  change dist (halfSpacePlaneEmbedUHP p.val u hu0 z).val
    (halfSpacePlaneEmbedUHP p.val u hu0 w).val = dist (z : ℂ) (w : ℂ) at hnorm
  rw [hp, hq, dist_eq_norm] at hnorm
  have hz := halfSpacePlaneEmbed_height p.val u hu0 (z : ℂ)
  have hw := halfSpacePlaneEmbed_height p.val u hu0 (w : ℂ)
  change halfSpaceHeight n (halfSpacePlaneEmbedUHP p.val u hu0 z).val = z.im at hz
  change halfSpaceHeight n (halfSpacePlaneEmbedUHP p.val u hu0 w).val = w.im at hw
  rw [hp] at hz
  rw [hq] at hw
  rw [hdist, UpperHalfPlane.dist_eq, ← hnorm, ← hz, ← hw]

theorem halfSpacePathDist_sinh_half {n : ℕ} (hn : 1 ≤ n) (p q : HyperbolicHalfSpace n) :
    Real.sinh (halfSpacePathDist p q / 2) = ‖p.val - q.val‖ /
      (2 * Real.sqrt (halfSpaceHeight n p.val * halfSpaceHeight n q.val)) := by
  rw [halfSpacePathDist_eq_arsinh hn p q, mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh]


/-- Euclidean centre of the hyperbolic sphere from. -/
def halfSpaceSphereCenter {n : ℕ} (p : HyperbolicHalfSpace n) (r : ℝ) : Inversive.Euclidean (n + 1) :=
  p.val + (p.val (Fin.last n) * (Real.cosh r - 1)) • verticalUnitVector n

theorem halfSpaceSphereCenter_height {n : ℕ} (p : HyperbolicHalfSpace n) (r : ℝ) :
    halfSpaceSphereCenter p r (Fin.last n) = p.val (Fin.last n) * Real.cosh r := by
  simp only [halfSpaceSphereCenter, PiLp.add_apply, PiLp.smul_apply, verticalUnitVector,
    PiLp.single_eq_same, smul_eq_mul, mul_one]
  ring

theorem halfSpaceSphereCenter_dist_sq {n : ℕ} (hn : 1 ≤ n)
    (p q : HyperbolicHalfSpace n) (r : ℝ) :
    dist q.val (halfSpaceSphereCenter p r) ^ 2 =
      2 * p.val (Fin.last n) * q.val (Fin.last n) *
        (Real.cosh (halfSpacePathDist p q) - Real.cosh r) +
          (p.val (Fin.last n) * Real.sinh r) ^ 2 := by
  have hprod : 2 * p.val (Fin.last n) * q.val (Fin.last n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) p.property.ne') q.property.ne'
  have hcos : Real.cosh (halfSpacePathDist p q) - 1 =
      ‖q.val - p.val‖ ^ 2 / (2 * p.val (Fin.last n) * q.val (Fin.last n)) := by
    rw [halfSpacePathDist_cosh hn, halfSpaceHeight_apply, halfSpaceHeight_apply, norm_sub_rev]
    ring
  have hsq := (eq_div_iff hprod).mp hcos
  have hinner : inner ℝ (q.val - p.val) (verticalUnitVector n) =
      q.val (Fin.last n) - p.val (Fin.last n) := by
    simp [verticalUnitVector, EuclideanSpace.inner_single_right, PiLp.sub_apply]
  rw [dist_eq_norm, halfSpaceSphereCenter]
  rw [show q.val - (p.val + (p.val (Fin.last n) * (Real.cosh r - 1)) • verticalUnitVector n) =
      (q.val - p.val) - (p.val (Fin.last n) * (Real.cosh r - 1)) • verticalUnitVector n by abel]
  rw [norm_sub_sq_real, inner_smul_right, hinner, norm_smul, norm_verticalUnitVector,
    mul_one, Real.norm_eq_abs, sq_abs, ← hsq]
  simp only [mul_pow, Real.sinh_sq]
  ring

/-- The exact hyperbolic-sphere / Euclidean-sphere equation. -/
theorem halfSpacePathDist_eq_radius_iff {n : ℕ} (hn : 1 ≤ n)
    (p q : HyperbolicHalfSpace n) (r : ℝ) (hr : 0 ≤ r) :
    halfSpacePathDist p q = r ↔
      dist q.val (halfSpaceSphereCenter p r) = p.val (Fin.last n) * Real.sinh r := by
  have hsq := halfSpaceSphereCenter_dist_sq hn p q r
  have hrad : 0 ≤ p.val (Fin.last n) * Real.sinh r :=
    mul_nonneg p.property.le (Real.sinh_nonneg_iff.mpr hr)
  constructor
  · intro heq
    rw [heq, sub_self, mul_zero, zero_add] at hsq
    exact (sq_eq_sq₀ dist_nonneg hrad).mp hsq
  · intro heq
    rw [heq] at hsq
    have hpos : 0 < 2 * p.val (Fin.last n) * q.val (Fin.last n) :=
      mul_pos (mul_pos (by norm_num) p.property) q.property
    have hcosh : Real.cosh (halfSpacePathDist p q) = Real.cosh r := by nlinarith
    exact Real.cosh_strictMonoOn.injOn (halfSpacePathDist_metric_axioms p q q).1 hr hcosh

/-- The entire associated Euclidean sphere lies strictly above the Euclidean boundary. -/
theorem halfSpaceSphere_subset_domain {n : ℕ} (p : HyperbolicHalfSpace n) (r : ℝ)
    {x : Inversive.Euclidean (n + 1)}
    (hx : dist x (halfSpaceSphereCenter p r) = p.val (Fin.last n) * Real.sinh r) :
    x ∈ upperHalfSpaceDomain n := by
  have hh : |x (Fin.last n) - halfSpaceSphereCenter p r (Fin.last n)| ≤
      dist x (halfSpaceSphereCenter p r) := by
    simpa only [Real.norm_eq_abs, PiLp.sub_apply, dist_eq_norm] using
      (PiLp.norm_apply_le (x - halfSpaceSphereCenter p r) (Fin.last n))
  rw [hx, halfSpaceSphereCenter_height] at hh
  have hlow := (abs_le.mp hh).1
  have hpos : 0 < p.val (Fin.last n) * (Real.cosh r - Real.sinh r) := by
    apply mul_pos p.property
    rw [Real.cosh_sub_sinh]
    exact Real.exp_pos _
  change 0 < x (Fin.last n)
  linarith

/-- as equality with the full Euclidean sphere rather than a domain restriction. -/
theorem halfSpaceSphere_eq_euclideanSphere {n : ℕ} (hn : 1 ≤ n)
    (p : HyperbolicHalfSpace n) (r : ℝ) (hr : 0 ≤ r) :
    (Subtype.val : HyperbolicHalfSpace n → Inversive.Euclidean (n + 1)) ''
      {q : HyperbolicHalfSpace n | halfSpacePathDist p q = r} =
        Metric.sphere (halfSpaceSphereCenter p r) (p.val (Fin.last n) * Real.sinh r) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (halfSpacePathDist_eq_radius_iff hn p q r hr).mp hq
  · intro hx
    have hmem := halfSpaceSphere_subset_domain p r hx
    exact ⟨⟨x, hmem⟩, (halfSpacePathDist_eq_radius_iff hn p ⟨x, hmem⟩ r hr).mpr hx, rfl⟩


open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic

section PlaneEquality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal coordinates split the squared norm into the in-plane and normal parts. -/
theorem twoPlane_norm_sq_decomposition (u e : E) (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (hue : ⟪u, e⟫_ℝ = 0) (v : E) :
    ‖v‖ ^ 2 = ‖twoPlaneProjectCLM u e v‖ ^ 2 +
      ‖v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)‖ ^ 2 := by
  have heu : ⟪e, u⟫_ℝ = 0 := by rw [real_inner_comm, hue]
  have hru : ⟪u, v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)⟫_ℝ = 0 := by
    simp [twoPlaneEmbedCLM_apply, twoPlaneProjectCLM_re, twoPlaneProjectCLM_im, inner_sub_right, inner_add_right,
      real_inner_smul_right, hu, hue]
  have hre : ⟪e, v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)⟫_ℝ = 0 := by
    simp [twoPlaneEmbedCLM_apply, twoPlaneProjectCLM_re, twoPlaneProjectCLM_im, inner_sub_right, inner_add_right,
      real_inner_smul_right, he, heu]
  have horth : ⟪twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v),
      v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)⟫_ℝ = 0 := by
    change ⟪(twoPlaneProjectCLM u e v).re • u + (twoPlaneProjectCLM u e v).im • e,
      v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)⟫_ℝ = 0
    simp only [inner_add_left, real_inner_smul_left, hru, hre, mul_zero, add_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ)
    (twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v))
    (v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)) horth
  have hsum : twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v) +
      (v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)) = v := by abel
  rw [hsum, twoPlaneEmbedCLM_norm u e hu he hue] at hp
  simpa only [pow_two] using hp

theorem twoPlaneProjectCLM_norm_eq_iff (u e : E) (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (hue : ⟪u, e⟫_ℝ = 0) (v : E) :
    ‖twoPlaneProjectCLM u e v‖ = ‖v‖ ↔
      twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v) = v := by
  constructor
  · intro h
    have hp := twoPlane_norm_sq_decomposition u e hu he hue v
    rw [h] at hp
    have hz : ‖v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v)‖ = 0 := by
      nlinarith [norm_nonneg (v - twoPlaneEmbedCLM u e (twoPlaneProjectCLM u e v))]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro h
    simpa only [h] using (twoPlaneEmbedCLM_norm u e hu he hue (twoPlaneProjectCLM u e v)).symm

end PlaneEquality

/-- Equality in the Euclidean projection estimate characterizes membership in the plane. -/
theorem halfSpacePlaneProject_dist_eq_iff {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (z : ℂ) (v : Inversive.Euclidean (n + 1)) :
    dist z (halfSpacePlaneProject x u v) = dist (halfSpacePlaneEmbed x u z) v ↔
      halfSpacePlaneEmbed x u (halfSpacePlaneProject x u v) = v := by
  have hdiff : halfSpacePlaneProjectCLM u (v - halfSpacePlaneEmbed x u z) =
      halfSpacePlaneProject x u v - z := by
    calc
      _ = halfSpacePlaneProject x u v - halfSpacePlaneProject x u (halfSpacePlaneEmbed x u z) := by
        dsimp only [halfSpacePlaneProject]
        rw [← map_sub]
        congr 1
        abel
      _ = _ := by rw [halfSpacePlaneProject_embed x u hu hu0 z]

  have hsum : halfSpacePlaneEmbedCLM u
      (halfSpacePlaneProjectCLM u (v - halfSpacePlaneEmbed x u z)) =
      v - halfSpacePlaneEmbed x u z ↔
      halfSpacePlaneEmbed x u (halfSpacePlaneProject x u v) = v := by
    rw [hdiff, map_sub]
    dsimp only [halfSpacePlaneEmbed]
    constructor
    · intro h
      have h' : halfSpacePlaneEmbedCLM u (halfSpacePlaneProject x u v) =
          v - halfSpaceHorizontalPart x := by
        calc
          _ = (halfSpacePlaneEmbedCLM u (halfSpacePlaneProject x u v) -
              halfSpacePlaneEmbedCLM u z) + halfSpacePlaneEmbedCLM u z := by abel
          _ = (v - (halfSpaceHorizontalPart x + halfSpacePlaneEmbedCLM u z)) +
              halfSpacePlaneEmbedCLM u z := congrArg (· + halfSpacePlaneEmbedCLM u z) h
          _ = _ := by abel
      rw [h']
      abel
    · intro h
      have h' : halfSpacePlaneEmbedCLM u (halfSpacePlaneProject x u v) =
          v - halfSpaceHorizontalPart x := by
        apply (eq_sub_iff_add_eq).mpr
        simpa only [add_comm] using h
      rw [h']
      abel
  rw [dist_comm z, dist_comm (halfSpacePlaneEmbed x u z), dist_eq_norm, dist_eq_norm,
    ← hdiff]
  exact (twoPlaneProjectCLM_norm_eq_iff u (halfSpaceVerticalUnit n) hu
    (halfSpaceVerticalUnit_norm n) (by rw [inner_halfSpaceVerticalUnit, hu0])
      (v - halfSpacePlaneEmbed x u z)).trans hsum

/-- Equality in hyperbolic projection also forces the point to lie in the plane. -/
theorem halfSpacePlaneProject_pathDist_eq_iff {n : ℕ} (hn : 1 ≤ n)
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (z : ℍ) (p : HyperbolicHalfSpace n) :
    dist z (halfSpacePlaneProjectUHP x u p) =
        halfSpacePathDist (halfSpacePlaneEmbedUHP x u hu0 z) p ↔
      halfSpacePlaneEmbedUHP x u hu0 (halfSpacePlaneProjectUHP x u p) = p := by
  constructor
  · intro h
    have hc := congrArg Real.cosh h
    rw [UpperHalfPlane.cosh_dist, halfSpacePathDist_cosh hn] at hc
    have hz : halfSpaceHeight n (halfSpacePlaneEmbedUHP x u hu0 z).val = z.im :=
      halfSpacePlaneEmbed_height x u hu0 z
    rw [hz, halfSpacePlaneProjectUHP_im] at hc
    have hd : 2 * z.im * halfSpaceHeight n p.val ≠ 0 :=
      (mul_pos (mul_pos (by norm_num) z.im_pos) p.property).ne'
    have hs := (div_left_inj' hd).mp (add_left_cancel hc)
    have hnrm : dist (z : ℂ) (halfSpacePlaneProject x u p.val) =
        dist (halfSpacePlaneEmbed x u z) p.val := by
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      exact hs
    apply Subtype.ext
    exact (halfSpacePlaneProject_dist_eq_iff x u hu hu0 z p.val).mp hnrm
  · intro h
    rw [← h, halfSpacePlaneEmbed_pathDist x u hu hu0]
    rw [halfSpacePlaneProjectUHP_embed x u hu hu0]

/-- Any point realizing equality in the ambient triangle inequality lies in the common plane. -/
theorem halfSpace_triangle_eq_implies_plane {n : ℕ} (hn : 1 ≤ n)
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (z w : ℍ) (p : HyperbolicHalfSpace n)
    (heq : halfSpacePathDist (halfSpacePlaneEmbedUHP x u hu0 z) p +
      halfSpacePathDist p (halfSpacePlaneEmbedUHP x u hu0 w) = dist z w) :
    halfSpacePlaneEmbedUHP x u hu0 (halfSpacePlaneProjectUHP x u p) = p := by
  have hp := halfSpacePlaneProject_dist_le_pathDist x u hu hu0
    (halfSpacePlaneEmbedUHP x u hu0 z) p
  have hq := halfSpacePlaneProject_dist_le_pathDist x u hu hu0
    p (halfSpacePlaneEmbedUHP x u hu0 w)
  rw [halfSpacePlaneProjectUHP_embed x u hu hu0] at hp hq
  have ht := dist_triangle z (halfSpacePlaneProjectUHP x u p) w
  apply (halfSpacePlaneProject_pathDist_eq_iff hn x u hu hu0 z p).mp
  linarith


/-- Complete geodesics in an actual ambient vertical plane. -/
def halfSpacePlaneSL2Geodesic {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (a t : ℝ) : HyperbolicHalfSpace n :=
  halfSpacePlaneEmbedUHP x u hu0 (halfPlaneSL2Geodesic g a t)

theorem halfSpacePlaneSL2Geodesic_pathDist {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a s t : ℝ) :
    halfSpacePathDist (halfSpacePlaneSL2Geodesic x u hu0 g a s)
      (halfSpacePlaneSL2Geodesic x u hu0 g a t) = dist s t := by
  rw [halfSpacePlaneSL2Geodesic, halfSpacePlaneSL2Geodesic,
    halfSpacePlaneEmbed_pathDist x u hu hu0]
  exact (halfPlaneSL2Geodesic_isometry g a).dist_eq s t

theorem halfSpace_triangle_eq_iff_geodesic_interval {n : ℕ} (hn : 1 ≤ n)
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z w : ℍ)
    (hre : (g • z).re = (g • w).re) (p : HyperbolicHalfSpace n) :
    halfSpacePathDist (halfSpacePlaneEmbedUHP x u hu0 z) p +
        halfSpacePathDist p (halfSpacePlaneEmbedUHP x u hu0 w) =
        halfSpacePathDist (halfSpacePlaneEmbedUHP x u hu0 z)
          (halfSpacePlaneEmbedUHP x u hu0 w) ↔
      p ∈ halfSpacePlaneSL2Geodesic x u hu0 g (g • z).re ''
        uIcc (Real.log (g • z).im) (Real.log (g • w).im) := by
  constructor
  · intro h
    rw [halfSpacePlaneEmbed_pathDist x u hu hu0] at h
    have hp := halfSpace_triangle_eq_implies_plane hn x u hu hu0 z w p h
    have hleft := halfSpacePlaneEmbed_pathDist x u hu hu0 z (halfSpacePlaneProjectUHP x u p)
    have hright := halfSpacePlaneEmbed_pathDist x u hu hu0 (halfSpacePlaneProjectUHP x u p) w
    rw [hp] at hleft hright
    have heq : dist z (halfSpacePlaneProjectUHP x u p) +
        dist (halfSpacePlaneProjectUHP x u p) w = dist z w := by linarith
    obtain ⟨r, hr, hΓr⟩ :=
      (halfPlane_triangle_eq_iff_geodesic_interval g z w _ hre).mp heq
    refine ⟨r, hr, ?_⟩
    dsimp only [halfSpacePlaneSL2Geodesic]
    rw [hΓr, hp]
  · rintro ⟨r, hr, rfl⟩
    simp only [halfSpacePlaneSL2Geodesic, halfSpacePlaneEmbed_pathDist x u hu hu0]
    exact (halfPlane_triangle_eq_iff_geodesic_interval g z w _ hre).mpr ⟨r, hr, rfl⟩

/-- Every pair has a genuine complete metric geodesic, and its interval is exactly the
triangle-equality locus, including all ambient intermediate points. -/
theorem exists_halfSpace_geodesic_interval {n : ℕ} (hn : 1 ≤ n) (p q : HyperbolicHalfSpace n) :
    ∃ (Γ : ℝ → HyperbolicHalfSpace n) (s t : ℝ),
      (∀ a b, halfSpacePathDist (Γ a) (Γ b) = dist a b) ∧ Γ s = p ∧ Γ t = q ∧
      ∀ r : HyperbolicHalfSpace n,
        halfSpacePathDist p r + halfSpacePathDist r q = halfSpacePathDist p q ↔
          r ∈ Γ '' uIcc s t := by
  obtain ⟨u, hu0, hu, z, w, hp, hq⟩ := exists_halfSpacePlaneEmbedUHP_pair hn p q
  obtain ⟨g, hg⟩ := exists_sl2_same_real_part z w
  refine ⟨halfSpacePlaneSL2Geodesic p.val u hu0 g (g • z).re,
    Real.log (g • z).im, Real.log (g • w).im,
    halfSpacePlaneSL2Geodesic_pathDist p.val u hu hu0 g (g • z).re, ?_, ?_, ?_⟩
  · dsimp only [halfSpacePlaneSL2Geodesic]
    rw [halfPlaneSL2Geodesic_parameter g _ z rfl, hp]
  · dsimp only [halfSpacePlaneSL2Geodesic]
    rw [halfPlaneSL2Geodesic_parameter g _ w hg.symm, hq]
  · intro r
    have h := halfSpace_triangle_eq_iff_geodesic_interval hn p.val u hu hu0 g z w hg r
    rw [hp, hq] at h
    exact h


/-! ## Euclidean shapes of complete geodesics -/

/-- A genuine vertical Euclidean line or a Euclidean semicircle in a vertical two-plane.
The circle centre has zero height because its plane coordinate is real. -/
def IsHalfSpaceGeodesicLine (n : ℕ) (L : Set (HyperbolicHalfSpace n)) : Prop :=
  (∃ v : Inversive.Euclidean (n + 1), halfSpaceHeight n v = 0 ∧
    L = {p | halfSpaceHorizontalPart p.val = v}) ∨
  ∃ x u : Inversive.Euclidean (n + 1), ‖u‖ = 1 ∧ halfSpaceHeight n u = 0 ∧
    ∃ c r : ℝ, 0 < r ∧ L = {p | p.val ∈ range (halfSpacePlaneEmbed x u) ∧
      ‖p.val - halfSpacePlaneEmbed x u (c : ℂ)‖ = r}

theorem halfSpacePlaneEmbedUHP_vertical_image {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) (a : ℝ) :
    halfSpacePlaneEmbedUHP x u hu0 '' {z : ℍ | z.re = a} =
      {p : HyperbolicHalfSpace n |
        halfSpaceHorizontalPart p.val = halfSpaceHorizontalPart x + a • u} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    change halfSpacePlaneEmbed x u z -
      halfSpaceHeight n (halfSpacePlaneEmbed x u z) • halfSpaceVerticalUnit n = _
    rw [halfSpacePlaneEmbed_height x u hu0]
    simp only [halfSpacePlaneEmbed, halfSpacePlaneEmbedCLM, twoPlaneEmbedCLM_apply,
      show (z : ℂ).re = a from hz]
    abel
  · intro hp
    let z : ℍ := ⟨(a : ℂ) + (halfSpaceHeight n p.val : ℂ) * Complex.I, by
      simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero, zero_add] using
        (show 0 < halfSpaceHeight n p.val from p.property)⟩
    refine ⟨z, by simp [z], Subtype.ext ?_⟩
    change halfSpacePlaneEmbed x u (z : ℂ) = p.val
    calc
      _ = halfSpaceHorizontalPart x + a • u + halfSpaceHeight n p.val • halfSpaceVerticalUnit n := by
        simp only [z, halfSpacePlaneEmbed, halfSpacePlaneEmbedCLM,
          twoPlaneEmbedCLM_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          mul_zero, sub_zero, mul_one, add_zero, zero_add]
        abel
      _ = halfSpaceHorizontalPart p.val + halfSpaceHeight n p.val • halfSpaceVerticalUnit n := by
        rw [show halfSpaceHorizontalPart p.val = _ from hp]
      _ = p.val := by dsimp only [halfSpaceHorizontalPart]; abel

theorem halfSpacePlaneEmbedUHP_circle_image {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (c r : ℝ) :
    halfSpacePlaneEmbedUHP x u hu0 '' {z : ℍ | ‖(z : ℂ) - (c : ℂ)‖ = r} =
      {p : HyperbolicHalfSpace n | p.val ∈ range (halfSpacePlaneEmbed x u) ∧
        ‖p.val - halfSpacePlaneEmbed x u (c : ℂ)‖ = r} := by
  ext p
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨(z : ℂ), rfl⟩, ?_⟩
    have h := halfSpacePlaneEmbed_dist x u hu hu0 (z : ℂ) (c : ℂ)
    rw [dist_eq_norm, dist_eq_norm] at h
    exact h.trans hz
  · rintro ⟨⟨z, hz⟩, hs⟩
    have hzpos : 0 < z.im := by
      rw [← halfSpacePlaneEmbed_height x u hu0 z, hz]
      exact p.property
    refine ⟨⟨z, hzpos⟩, ?_, Subtype.ext hz⟩
    have h := halfSpacePlaneEmbed_dist x u hu hu0 z (c : ℂ)
    rw [hz, dist_eq_norm, dist_eq_norm] at h
    exact h.symm.trans hs

theorem halfSpacePlaneSL2Geodesic_range {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ) :
    range (halfSpacePlaneSL2Geodesic x u hu0 g a) =
      halfSpacePlaneEmbedUHP x u hu0 '' range (halfPlaneSL2Geodesic g a) :=
  Set.range_comp _ _

theorem halfSpacePlaneSL2Geodesic_isLine {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ) :
    IsHalfSpaceGeodesicLine n (range (halfSpacePlaneSL2Geodesic x u hu0 g a)) := by
  rcases halfPlaneSL2Geodesic_isLine g a with ⟨b, hb⟩ | ⟨c, r, hr, hc⟩
  · left
    refine ⟨halfSpaceHorizontalPart x + b • u, ?_, ?_⟩
    · simp [halfSpaceHeight_horizontalPart, hu0]
    · rw [halfSpacePlaneSL2Geodesic_range, hb, halfSpacePlaneEmbedUHP_vertical_image]
  · right
    refine ⟨x, u, hu, hu0, c, r, hr, ?_⟩
    rw [halfSpacePlaneSL2Geodesic_range, hc, halfSpacePlaneEmbedUHP_circle_image x u hu hu0]

/-- A complete, genuinely Euclidean vertical or semicircular metric geodesic through any pair;
the intrinsic triangle-equality locus is its actual parameter interval. -/
theorem exists_halfSpace_geodesic_geometry {n : ℕ} (hn : 1 ≤ n)
    (p q : HyperbolicHalfSpace n) :
    ∃ (Γ : ℝ → HyperbolicHalfSpace n) (s t : ℝ),
      (∀ a b, halfSpacePathDist (Γ a) (Γ b) = dist a b) ∧
      IsHalfSpaceGeodesicLine n (range Γ) ∧ Γ s = p ∧ Γ t = q ∧
      ∀ r : HyperbolicHalfSpace n,
        halfSpacePathDist p r + halfSpacePathDist r q = halfSpacePathDist p q ↔
          r ∈ Γ '' uIcc s t := by
  obtain ⟨u, hu0, hu, z, w, hp, hq⟩ := exists_halfSpacePlaneEmbedUHP_pair hn p q
  obtain ⟨g, hg⟩ := exists_sl2_same_real_part z w
  refine ⟨halfSpacePlaneSL2Geodesic p.val u hu0 g (g • z).re,
    Real.log (g • z).im, Real.log (g • w).im,
    halfSpacePlaneSL2Geodesic_pathDist p.val u hu hu0 g (g • z).re,
    halfSpacePlaneSL2Geodesic_isLine p.val u hu hu0 g (g • z).re, ?_, ?_, ?_⟩
  · dsimp only [halfSpacePlaneSL2Geodesic]
    rw [halfPlaneSL2Geodesic_parameter g _ z rfl, hp]
  · dsimp only [halfSpacePlaneSL2Geodesic]
    rw [halfPlaneSL2Geodesic_parameter g _ w hg.symm, hq]
  · intro r
    have h := halfSpace_triangle_eq_iff_geodesic_interval hn p.val u hu hu0 g z w hg r
    rw [hp, hq] at h
    exact h

/-! ## Minimizing curve and chain traces -/

open scoped ContDiff Topology ENNReal

theorem halfSpace_curve_distance_sum_le_integral {n : ℕ}
    (γ : ℝ → HyperbolicHalfSpace n) (ν : ℝ → Inversive.Euclidean (n + 1))
    (a b : ℝ) (_hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => (γ s).val) (ν t) (Icc a b) t)
    (hspeed : ContinuousOn (fun t => halfSpaceDensity n (γ t) * ‖ν t‖) (Icc a b))
    (t : ℝ) (ht : t ∈ Icc a b) :
    halfSpacePathDist (γ a) (γ t) + halfSpacePathDist (γ t) (γ b) ≤
      ∫ s in a..b, halfSpaceDensity n (γ s) * ‖ν s‖ := by
  have hL : Icc a t ⊆ Icc a b := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hR : Icc t b ⊆ Icc a b := fun _ hs => ⟨ht.1.trans hs.1, hs.2⟩
  have hlo := (halfSpaceDensity n).pathDist_le_integral_of_continuous_speed γ ν a t ht.1
    (hγ.mono hL) (fun s hs => (hd s (hL hs)).mono hL) (hspeed.mono hL)
  have hhi := (halfSpaceDensity n).pathDist_le_integral_of_continuous_speed γ ν t b ht.2
    (hγ.mono hR) (fun s hs => (hd s (hR hs)).mono hR) (hspeed.mono hR)
  exact (add_le_add hlo hhi).trans_eq (intervalIntegral.integral_add_adjacent_intervals
    ((hspeed.mono hL).intervalIntegrable_of_Icc ht.1)
    ((hspeed.mono hR).intervalIntegrable_of_Icc ht.2))

theorem halfSpace_piece_distance_sum_le {n : ℕ}
    (γ : ℝ → HyperbolicHalfSpace n) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1 γ (Icc a b))
    (t : ℝ) (ht : t ∈ Icc a b) :
    halfSpacePathDist (γ a) (γ t) + halfSpacePathDist (γ t) (γ b) ≤
      (halfSpacePieceLength γ a b).toReal := by
  rw [halfSpacePieceLength_eq_coordinate_integral γ a b hab hγ,
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hab
      (fun s _ => div_nonneg (norm_nonneg _) (γ s).property.le))]
  rcases hab.eq_or_lt with rfl | hab
  · have hta : t = a := le_antisymm ht.2 ht.1
    subst t
    simp [halfSpacePathDist, Auxiliary.Analysis.Density.pathDist_self]
  let ν := derivWithin (fun s => (γ s).val) (Icc a b)
  have hc := (Auxiliary.Analysis.openDomain_contDiffOn_ambient hγ).continuousOn_derivWithin
    (uniqueDiffOn_Icc hab) le_rfl
  have hbound := halfSpace_curve_distance_sum_le_integral γ ν a b hab.le hγ.continuousOn
    (fun s hs => ((Auxiliary.Analysis.openDomain_contDiffOn_ambient hγ).differentiableOn
      one_ne_zero s hs).hasDerivWithinAt)
    (((halfSpaceDensity n).continuous.comp_continuousOn hγ.continuousOn).mul hc.norm) t ht
  apply hbound.trans_eq
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [ν]
  rw [halfSpaceDensity_apply]
  ring

/-- The actual point trace of a finite admissible C1 chain. -/
def halfSpaceChainTrace {n : ℕ} {p q : HyperbolicHalfSpace n} :
    Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q →
      Set (HyperbolicHalfSpace n)
  | .nil p => {p}
  | .cons γ a b _ _ _ _ tail => γ '' Icc a b ∪ halfSpaceChainTrace tail

theorem halfSpaceChainTrace_start_mem {n : ℕ} {p q : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q) :
    p ∈ halfSpaceChainTrace c := by
  cases c with
  | nil p => exact mem_singleton p
  | cons γ a b hab hc ha hb tail =>
    exact Or.inl ⟨a, left_mem_Icc.mpr hab, ha⟩

theorem halfSpaceChainTrace_end_mem {n : ℕ} {p q : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q) :
    q ∈ halfSpaceChainTrace c := by
  induction c with
  | nil p => exact mem_singleton p
  | cons γ a b hab hc ha hb tail ih => exact Or.inr ih

theorem halfSpaceChainTrace_isPreconnected {n : ℕ} {p q : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q) :
    IsPreconnected (halfSpaceChainTrace c) := by
  induction c with
  | nil p => exact isPreconnected_singleton
  | cons γ a b hab hc ha hb tail ih =>
    apply IsPreconnected.union' _ (isPreconnected_Icc.image γ hc.continuousOn) ih
    refine ⟨γ b, ⟨b, right_mem_Icc.mpr hab, rfl⟩, ?_⟩
    rw [hb]
    exact halfSpaceChainTrace_start_mem tail

/-- Every point of a chain satisfies the broken-distance lower bound for its total integral. -/
theorem halfSpaceChainTrace_distance_sum_le {n : ℕ} {p q : HyperbolicHalfSpace n}
    (c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q)
    (r : HyperbolicHalfSpace n) (hr : r ∈ halfSpaceChainTrace c) :
    halfSpacePathDist p r + halfSpacePathDist r q ≤ (halfSpaceChainLength c).toReal := by
  induction c with
  | nil p =>
    have heq : r = p := hr
    subst r
    simp [halfSpacePathDist, Auxiliary.Analysis.Density.pathDist_self,
      halfSpaceChainLength, Auxiliary.Analysis.Density.chainLength]
  | @cons p v q γ a b hab hc ha hb tail ih =>
    have hlen : (halfSpaceChainLength (.cons γ a b hab hc ha hb tail)).toReal =
        (halfSpacePieceLength γ a b).toReal + (halfSpaceChainLength tail).toReal := by
      simp only [halfSpaceChainLength, Auxiliary.Analysis.Density.chainLength, halfSpacePieceLength,
        ENNReal.toReal_add ((halfSpaceDensity n).pieceLength_ne_top γ a b hab hc)
          ((halfSpaceDensity n).chainLength_ne_top tail)]
    rw [hlen]
    rcases hr with ⟨t, ht, rfl⟩ | hr
    · have hmid := halfSpace_piece_distance_sum_le γ a b hab hc t ht
      rw [ha, hb] at hmid
      have htail := halfSpacePathDist_comp_chain_le (fun z => z) continuous_id
        (fun _ _ => rfl) tail
      have htri := (halfSpaceDensity n).pathDist_triangle (γ t) v q
      change halfSpacePathDist (γ t) q ≤ halfSpacePathDist (γ t) v + halfSpacePathDist v q at htri
      change halfSpacePathDist v q ≤ (halfSpaceChainLength tail).toReal at htail
      linarith
    · have hi := ih hr
      have hpiece := halfSpacePathDist_comp_piece_le (fun z => z) continuous_id
        (fun _ _ => rfl) γ a b hab hc
      rw [ha, hb] at hpiece
      have htri := (halfSpaceDensity n).pathDist_triangle p v r
      change halfSpacePathDist p r ≤ halfSpacePathDist p v + halfSpacePathDist v r at htri
      linarith

theorem real_dist_left_injective_on_uIcc (s t a b : ℝ) (ha : a ∈ uIcc s t)
    (hb : b ∈ uIcc s t) (hd : dist s a = dist s b) : a = b := by
  rcases le_total s t with hst | hts
  · rw [uIcc_of_le hst] at ha hb
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ha.1),
      abs_of_nonpos (sub_nonpos.mpr hb.1)] at hd
    linarith
  · rw [uIcc_of_ge hts] at ha hb
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ha.2),
      abs_of_nonneg (sub_nonneg.mpr hb.2)] at hd
    linarith

/-- A connected subset of a geodesic interval containing both endpoints is the whole arc. -/
theorem halfSpace_geodesic_arc_eq_of_preconnected {n : ℕ}
    (Γ : ℝ → HyperbolicHalfSpace n) (hΓ : ∀ a b, halfSpacePathDist (Γ a) (Γ b) = dist a b)
    (s t : ℝ) (S : Set (HyperbolicHalfSpace n)) (hS : IsPreconnected S)
    (hs : Γ s ∈ S) (ht : Γ t ∈ S) (hsub : S ⊆ Γ '' uIcc s t) :
    S = Γ '' uIcc s t := by
  apply Subset.antisymm hsub
  rintro _ ⟨r, hr, rfl⟩
  have hv : dist s r ∈ Icc (halfSpacePathDist (Γ s) (Γ s))
      (halfSpacePathDist (Γ s) (Γ t)) := by
    rw [hΓ, hΓ, dist_self]
    exact ⟨dist_nonneg, Real.dist_left_le_of_mem_uIcc hr⟩
  obtain ⟨p, hp, hdist⟩ := hS.intermediate_value hs ht
    ((halfSpaceDensity n).continuous_pathDist_left (Γ s)).continuousOn hv
  obtain ⟨a, ha, hpa⟩ := hsub hp
  rw [← hpa] at hdist
  change halfSpacePathDist (Γ s) (Γ a) = dist s r at hdist
  rw [hΓ] at hdist
  have heq := real_dist_left_injective_on_uIcc s t a r ha hr hdist
  rw [← heq, hpa]
  exact hp

/-- Every finite C1 chain attaining the genuine length infimum has the same unparametrized arc.
Pauses and the finitely many allowed derivative breaks do not affect this uniqueness statement. -/
theorem exists_halfSpace_unique_minimizing_trace {n : ℕ} (hn : 1 ≤ n)
    (p q : HyperbolicHalfSpace n) :
    ∃ (Γ : ℝ → HyperbolicHalfSpace n) (s t : ℝ),
      (∀ a b, halfSpacePathDist (Γ a) (Γ b) = dist a b) ∧
      IsHalfSpaceGeodesicLine n (range Γ) ∧ Γ s = p ∧ Γ t = q ∧
      ∀ c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q,
        (halfSpaceChainLength c).toReal = halfSpacePathDist p q →
          halfSpaceChainTrace c = Γ '' uIcc s t := by
  obtain ⟨Γ, s, t, hΓ, hLine, hp, hq, hLocus⟩ := exists_halfSpace_geodesic_geometry hn p q
  refine ⟨Γ, s, t, hΓ, hLine, hp, hq, ?_⟩
  intro c hc
  apply halfSpace_geodesic_arc_eq_of_preconnected Γ hΓ s t _ (halfSpaceChainTrace_isPreconnected c)
  · rw [hp]
    exact halfSpaceChainTrace_start_mem c
  · rw [hq]
    exact halfSpaceChainTrace_end_mem c
  · intro r hr
    have hbound := halfSpaceChainTrace_distance_sum_le c r hr
    rw [hc] at hbound
    apply (hLocus r).mp
    exact le_antisymm hbound ((halfSpaceDensity n).pathDist_triangle p r q)

theorem halfSpacePlaneEmbedUHP_piece_contMDiffOn {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu0 : halfSpaceHeight n u = 0)
    (c : C1CurvePiece) (hab : c.a < c.b) :
    ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1
      (halfSpacePlaneEmbedUHP x u hu0 ∘ c.curve) (Icc c.a c.b) := by
  have hc : ContDiffOn ℝ 1 (fun t => (c.curve t : ℂ)) (Icc c.a c.b) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
    refine ⟨fun t ht => (c.hasDerivWithin t ht).differentiableWithinAt, ?_⟩
    exact c.continuous_velocity.congr (fun t ht =>
      (c.hasDerivWithin t ht).derivWithin (uniqueDiffOn_Icc hab t ht))
  have he : ContDiff ℝ 1 (halfSpacePlaneEmbed x u) :=
    contDiff_const.add (halfSpacePlaneEmbedCLM u).contDiff
  have hcoord := he.comp_contDiffOn hc
  intro t ht
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp 𝓘(ℝ) 𝓘(ℝ, Inversive.Euclidean (n + 1)) 1)
    (halfSpacePlaneEmbedUHP x u hu0 ∘ c.curve) (Icc c.a c.b) t).mp
  exact (hcoord t ht).contMDiffWithinAt

theorem halfSpacePlaneEmbedUHP_piece_length {n : ℕ}
    (x u : Inversive.Euclidean (n + 1)) (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0)
    (c : C1CurvePiece) (hab : c.a < c.b) :
    halfSpacePieceLength (halfSpacePlaneEmbedUHP x u hu0 ∘ c.curve) c.a c.b =
      ENNReal.ofReal c.length := by
  rw [halfSpacePieceLength_eq_coordinate_integral _ _ _ hab.le
    (halfSpacePlaneEmbedUHP_piece_contMDiffOn x u hu0 c hab)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc c.a c.b := by simpa only [uIcc_of_le hab.le] using ht
  have hf : HasFDerivAt (halfSpacePlaneEmbed x u) (halfSpacePlaneEmbedCLM u) (c.curve t : ℂ) :=
    halfSpacePlaneEmbed_hasFDerivAt x u (c.curve t : ℂ)
  have hd : HasDerivWithinAt (halfSpacePlaneEmbed x u ∘ fun s => (c.curve s : ℂ))
      (halfSpacePlaneEmbedCLM u (c.velocity t)) (Icc c.a c.b) t :=
    hf.comp_hasDerivWithinAt t (c.hasDerivWithin t ht')
  change ‖derivWithin (halfSpacePlaneEmbed x u ∘ fun s => (c.curve s : ℂ)) (Icc c.a c.b) t‖ /
    halfSpaceHeight n (halfSpacePlaneEmbed x u (c.curve t)) = _
  rw [hd.derivWithin (uniqueDiffOn_Icc hab t ht'), halfSpacePlaneEmbedCLM_norm u hu hu0]
  rw [halfSpacePlaneEmbed_height x u hu0]
  rfl

/-- The actual finite C1-chain infimum is attained, not merely approached. -/
theorem exists_halfSpace_minimizing_chain {n : ℕ} (hn : 1 ≤ n) (p q : HyperbolicHalfSpace n) :
    ∃ c : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q,
      (halfSpaceChainLength c).toReal = halfSpacePathDist p q := by
  by_cases hpq : p = q
  · subst q
    exact ⟨.nil p, by simp [halfSpaceChainLength, Auxiliary.Analysis.Density.chainLength,
      halfSpacePathDist, Auxiliary.Analysis.Density.pathDist_self]⟩
  obtain ⟨u, hu0, hu, z, w, hp, hq⟩ := exists_halfSpacePlaneEmbedUHP_pair hn p q
  have hzw : z ≠ w := by
    intro h
    apply hpq
    rw [← hp, ← hq, h]
  obtain ⟨c, ha, hb, hlen⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_length_minimizing_piece z w
  have hab : c.a < c.b := lt_of_le_of_ne c.ordered (by
    intro h
    apply hzw
    rw [← ha, ← hb, h])
  let δ := halfSpacePlaneEmbedUHP p.val u hu0 ∘ c.curve
  have hstart : δ c.a = p := by dsimp only [δ, Function.comp_def]; rw [ha, hp]
  have hend : δ c.b = q := by dsimp only [δ, Function.comp_def]; rw [hb, hq]
  let chain : Auxiliary.Analysis.RiemannianC1Chain 𝓘(ℝ, Inversive.Euclidean (n + 1)) (HyperbolicHalfSpace n) p q :=
    .cons δ c.a c.b hab.le (halfSpacePlaneEmbedUHP_piece_contMDiffOn p.val u hu0 c hab)
      hstart hend (.nil q)
  refine ⟨chain, ?_⟩
  change ((halfSpaceDensity n).pieceLength δ c.a c.b + 0).toReal = _
  rw [add_zero, ← halfSpacePieceLength,
    halfSpacePlaneEmbedUHP_piece_length p.val u hu hu0 c hab, hlen,
    ENNReal.toReal_ofReal dist_nonneg]
  have hdist := halfSpacePlaneEmbed_pathDist p.val u hu hu0 z w
  rw [hp, hq] at hdist
  exact hdist.symm

theorem halfPlane_verticalNormalizer_circle_iff (c r : ℝ) (hr : 0 < r) (z : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalNormalizer (c + r) • z).re = 1 / (2 * r) ↔
      ‖(z : ℂ) - (c : ℂ)‖ = r := by
  have hd : (z.re - (c + r)) ^ 2 + z.im ^ 2 ≠ 0 := by
    have : 0 < (z.re - (c + r)) ^ 2 + z.im ^ 2 := by positivity
    exact this.ne'
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalNormalizer_re, div_eq_div_iff hd (by positivity), one_mul,
    ← sq_eq_sq₀ (norm_nonneg _) hr.le, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  constructor <;> intro h <;> nlinarith

/-- Every Euclidean vertical line or perpendicular semicircle is one of the complete
distance-preserving upper-half-plane geodesics. -/
theorem halfPlane_geodesicLine_exists_param {L : Set ℍ} (hL : IsHalfPlaneGeodesicLine L) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ), range (halfPlaneSL2Geodesic g a) = L := by
  rcases hL with ⟨c, hc⟩ | ⟨c, r, hr, hc⟩
  · refine ⟨1, c, ?_⟩
    simpa only [halfPlaneSL2Geodesic_range, one_smul] using hc.symm
  · refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalNormalizer (c + r), 1 / (2 * r), ?_⟩
    rw [halfPlaneSL2Geodesic_range, hc]
    ext z
    exact halfPlane_verticalNormalizer_circle_iff c r hr z

/-- Conversely every stated Euclidean vertical line or perpendicular semicircle admits
a complete geodesic parametrization for the actual ambient length metric. -/
theorem halfSpace_geodesicLine_exists_param {n : ℕ} (hn : 1 ≤ n)
    {L : Set (HyperbolicHalfSpace n)} (hL : IsHalfSpaceGeodesicLine n L) :
    ∃ Γ : ℝ → HyperbolicHalfSpace n,
      (∀ a b, halfSpacePathDist (Γ a) (Γ b) = dist a b) ∧ range Γ = L := by
  rcases hL with ⟨v, hv, hL⟩ | ⟨x, u, hu, hu0, c, r, hr, hL⟩
  · obtain ⟨u, a, hu, hu0, _⟩ := exists_halfSpace_horizontal_direction hn 0 0
    refine ⟨halfSpacePlaneSL2Geodesic v u hu0 1 0,
      halfSpacePlaneSL2Geodesic_pathDist v u hu hu0 1 0, ?_⟩
    rw [halfSpacePlaneSL2Geodesic_range, halfPlaneSL2Geodesic_range]
    simp only [one_smul]
    rw [halfSpacePlaneEmbedUHP_vertical_image]
    simpa only [halfSpaceHorizontalPart, hv, zero_smul, sub_zero, add_zero] using hL.symm
  · obtain ⟨g, a, hga⟩ := halfPlane_geodesicLine_exists_param
      (L := {z : ℍ | ‖(z : ℂ) - (c : ℂ)‖ = r}) (Or.inr ⟨c, r, hr, rfl⟩)
    refine ⟨halfSpacePlaneSL2Geodesic x u hu0 g a,
      halfSpacePlaneSL2Geodesic_pathDist x u hu hu0 g a, ?_⟩
    rw [halfSpacePlaneSL2Geodesic_range, hga, halfSpacePlaneEmbedUHP_circle_image x u hu hu0]
    exact hL.symm



end
end LowDimensionalTopology.Geometry.Hyperbolic
