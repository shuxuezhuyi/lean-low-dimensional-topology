/-
Copyright (c) 2026 Wu Xiaobin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeRootHorizontalFlowContinuity

/-!
# Area preservation of the actual root-oriented time maps

The original surface integral is used on the full critical-trajectory
complement with its Borel subtype structure. Ambient measurability of that
complement or of its subsets is not assumed.

The natural-coordinate integral calculation adapts s26v_a_pair_core and
s26v_pair_average of Wu Xiaobin's Li-Zhong-QC-formalization,
LiZhongQC/Ch07/S26_TeichmullerUniqueness.lean, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
Here the actual root-oriented bijection gives a single translated image.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

open scoped Classical in
private theorem rootTimeMap_integral
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ (U : X → ENNReal), s26v_IsBorelInCharts U → ∀ t : ℝ,
      surfaceIntegral (q : X → ℂ → ℂ) (fun x z =>
        if hp : (chartAt ℂ x).symm z ∉ s26v_E (q : X → ℂ → ℂ) then
          U (nativeRootHorizontalTimeMap R q β t ⟨(chartAt ℂ x).symm z, hp⟩ : X)
        else U ((chartAt ℂ x).symm z)) =
      surfaceIntegral (q : X → ℂ → ℂ) (fun x z => U ((chartAt ℂ x).symm z)) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := R.toRiemannAtlas.isManifold
  intro U hU t
  have hqfun : (q : X → ℂ → ℂ) ≠ 0 := fun hzero => hq (Subtype.ext hzero)
  let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
  let F : ℝ → Ω → Ω := nativeRootHorizontalTimeMap R q β
  have hact := nativeRootHorizontalTimeMap_action R q β hβ
  have hleft (u : ℝ) (p : Ω) : F (-u) (F u p) = p := by
    calc
      F (-u) (F u p) = F (-u + u) p := (hact.2 (-u) u p).symm
      _ = p := by rw [neg_add_cancel]; exact hact.1 p
  have hright (u : ℝ) (p : Ω) : F u (F (-u) p) = p := by
    simpa only [neg_neg] using hleft (-u) p
  have hT : (0 : ℝ) ≤ |t| := abs_nonneg t
  have ht : t ∈ Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩
  obtain ⟨ρ, G, hfam⟩ := s26v_a_tubeFamily_exists q.property hqfun hT
  have hsign : ∀ k : ℕ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ w ∈ ball (0 : ℂ) (ρ k), ∀ r ∈ Icc (-|t|) |t|,
        ∀ hw : G k w ∉ s26v_E (q : X → ℂ → ℂ),
          (F r ⟨G k w, hw⟩ : X) = G k (w + ((σ * r : ℝ) : ℂ)) := by
    intro k
    obtain ⟨p₀, hG⟩ := hfam.1 k
    exact nativeRootHorizontalTimeMap_tube_sign R q β hβ |t| hT p₀ (ρ k) (G k) hG
  choose σ hσ hflow using hsign
  have hσt (k : ℕ) : σ k * t ∈ Icc (-|t|) |t| := by
    rcases hσ k with h | h
    · simpa only [h, one_mul] using ht
    · simpa only [h, neg_one_mul] using (show -t ∈ Icc (-|t|) |t| from
        ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  let S : ℕ → Set X := fun k =>
    G k '' ((fun w => w + ((σ k * t : ℝ) : ℂ)) '' s26v_a_W G ρ k)
  have hback (y : X) (hy : y ∉ s26v_E (q : X → ℂ → ℂ)) (k : ℕ)
      (hyk : y ∈ S k) : (F (-t) ⟨y, hy⟩ : X) ∈ G k '' s26v_a_W G ρ k := by
    obtain ⟨_, ⟨w, hw, rfl⟩, hwy⟩ := hyk
    obtain ⟨p₀, hG⟩ := hfam.1 k
    have hwE : G k w ∉ s26v_E (q : X → ℂ → ℂ) :=
      s26v_a_tube_not_mem_E q.property hG hw.1 (hσt k) (by rw [hwy]; exact hy)
    have heq : F t ⟨G k w, hwE⟩ = (⟨y, hy⟩ : Ω) :=
      Subtype.ext ((hflow k w hw.1 t ht hwE).trans hwy)
    have hsrc : (⟨G k w, hwE⟩ : Ω) = F (-t) ⟨y, hy⟩ := by
      calc
        (⟨G k w, hwE⟩ : Ω) = F (-t) (F t ⟨G k w, hwE⟩) := (hleft t _).symm
        _ = F (-t) ⟨y, hy⟩ := congrArg (F (-t)) heq
    exact ⟨w, hw, congrArg Subtype.val hsrc⟩
  have hcount (y : X) (hy : y ∉ s26v_E (q : X → ℂ → ℂ)) :
      ∑' k, (S k).indicator (fun _ : X => (1 : ENNReal)) y = 1 := by
    let x : Ω := F (-t) ⟨y, hy⟩
    obtain ⟨k, w, hw, hwx⟩ := s26v_a_W_cover hfam x.property
    have hwE : G k w ∉ s26v_E (q : X → ℂ → ℂ) := by rw [hwx]; exact x.property
    have hx : (⟨G k w, hwE⟩ : Ω) = x := Subtype.ext hwx
    have hfy : F t ⟨G k w, hwE⟩ = (⟨y, hy⟩ : Ω) := by
      rw [hx]
      exact hright t ⟨y, hy⟩
    have hk : y ∈ S k :=
      ⟨w + ((σ k * t : ℝ) : ℂ), ⟨w, hw, rfl⟩,
        (hflow k w hw.1 t ht hwE).symm.trans (congrArg Subtype.val hfy)⟩
    have hnot (j : ℕ) (hjk : j ≠ k) : y ∉ S j := by
      intro hyj
      exact Set.disjoint_left.1 (s26v_a_W_disjoint (G := G) (ρ := ρ) hjk)
        (hback y hy j hyj) (hback y hy k hk)
    calc
      ∑' j, (S j).indicator (fun _ : X => (1 : ENNReal)) y =
          (S k).indicator (fun _ : X => (1 : ENNReal)) y :=
        tsum_eq_single k (fun j hj => Set.indicator_of_notMem (hnot j hj) _)
      _ = 1 := Set.indicator_of_mem hk _
  let f : X → ENNReal := fun p =>
    if hp : p ∉ s26v_E (q : X → ℂ → ℂ) then U (F t ⟨p, hp⟩ : X) else U p
  have hpiece (k : ℕ) :
      ∫⁻ w in s26v_a_W G ρ k, f (G k w) =
        ∫⁻ w in s26v_a_W G ρ k, U (G k (w + ((σ k * t : ℝ) : ℂ))) := by
    have hWm := s26v_a_W_measurable q.property hT hfam k
    have hc := s26v_a_family_center q.property hT hfam k
    have hnull : volume {w | w ∈ s26v_a_W G ρ k ∧ G k w ∈ s26v_E (q : X → ℂ → ℂ)} = 0 :=
      s26v_a_null_preimage_all q.property isOpen_ball (fun w hw => hw.1) hWm hc.1 hc.2.1
        (s26v_E_null q.property hqfun)
    have hae : ∀ᵐ w ∂(volume.restrict (s26v_a_W G ρ k)), G k w ∉ s26v_E (q : X → ℂ → ℂ) := by
      rw [ae_iff, Measure.restrict_apply' hWm]
      exact measure_mono_null (t := {w | w ∈ s26v_a_W G ρ k ∧ G k w ∈ s26v_E (q : X → ℂ → ℂ)})
        (fun w hw => ⟨hw.2, not_not.1 hw.1⟩) hnull
    refine lintegral_congr_ae ?_
    filter_upwards [hae, ae_restrict_mem hWm] with w hwE hw
    dsimp only [f]
    rw [dite_eq_left hwE, hflow k w hw.1 t ht hwE]
  let H : ℕ → X → ENNReal := fun k p => U p * (S k).indicator (fun _ : X => 1) p
  have hHm : ∀ k x, AEMeasurable (fun z => H k ((chartAt ℂ x).symm z))
      (volume.restrict (chartAt ℂ x).target) := by
    intro k x
    obtain ⟨hnat, hinj, hsub⟩ := s26v_a_family_ball hfam k (hσt k)
    exact (s26v_a_aemeasurable_chart hU x).mul
      (s26v_a_aemeasurable_indicator isOpen_ball hsub
        (s26v_a_W_translate_measurable q.property hT hfam k _) hnat hinj x)
  have hshift (k : ℕ) :
      ∫⁻ w in s26v_a_W G ρ k, U (G k (w + ((σ k * t : ℝ) : ℂ))) =
        surfaceIntegral (q : X → ℂ → ℂ) (fun x z => H k ((chartAt ℂ x).symm z)) :=
    s26v_a_family_shift q.property hT hfam U k (hσt k)
  have htarget : surfaceIntegral (q : X → ℂ → ℂ)
      (fun x z => ∑' k, H k ((chartAt ℂ x).symm z)) =
        surfaceIntegral (q : X → ℂ → ℂ) (fun x z => U ((chartAt ℂ x).symm z)) := by
    refine s26v_a_surfaceIntegral_congr_off (q : X → ℂ → ℂ) (s26v_E (q : X → ℂ → ℂ))
      (s26v_E_null q.property hqfun) fun x p hp hpE => ?_
    simp only [(chartAt ℂ x).left_inv hp, H]
    rw [ENNReal.tsum_mul_left, hcount p hpE, mul_one]
  exact (s26v_a_dev_formula q.property hqfun hT hfam f).trans
    ((tsum_congr fun k => (hpiece k).trans (hshift k)).trans
      ((s26v_a_surfaceIntegral_tsum q.property H hHm).symm.trans htarget))

private theorem indicator_borelInCharts
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (B : Set X) (hB : @MeasurableSet X (borel X) B) :
    letI := R.toRiemannAtlas.toChartedSpace
    s26v_IsBorelInCharts (B.indicator (fun _ : X => (1 : ENNReal))) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  intro x
  let e := chartAt ℂ x
  have hcont : Continuous (e.target.domRestrict e.symm) := e.continuousOn_symm.domRestrict
  have hpre : MeasurableSet ((e.target.domRestrict e.symm) ⁻¹' B) := hB.preimage hcont.measurable
  obtain ⟨C, hCm, hC⟩ := MeasurableSpace.measurableSet_comap.1 hpre
  refine ⟨C.indicator (fun _ : ℂ => (1 : ENNReal)), measurable_const.indicator hCm, ?_⟩
  intro z hz
  have hmem : z ∈ C ↔ e.symm z ∈ B := by
    change (⟨z, hz⟩ : e.target) ∈ Subtype.val ⁻¹' C ↔ _
    rw [hC]
    rfl
  by_cases hzB : e.symm z ∈ B
  · rw [Set.indicator_of_mem hzB, Set.indicator_of_mem (hmem.mpr hzB)]
  · rw [Set.indicator_of_notMem hzB, Set.indicator_of_notMem (fun hzC => hzB (hmem.mp hzC))]

/-- Every fixed time is Borel measurable on Ω and preserves the original q-area
of every Borel subset of that actual critical-trajectory complement. -/
theorem nativeRootHorizontalTimeMap_measurable_preservesArea
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
    letI : MeasurableSpace Ω := borel Ω
    (∀ t : ℝ, Measurable (nativeRootHorizontalTimeMap R q β t)) ∧
      ∀ (t : ℝ) (A : Set Ω), MeasurableSet A →
        surfaceIntegral (q : X → ℂ → ℂ) (fun x z =>
          ((fun p : Ω => (p : X)) '' ((nativeRootHorizontalTimeMap R q β t) '' A)).indicator
            (fun _ : X => (1 : ENNReal)) ((chartAt ℂ x).symm z)) =
        surfaceIntegral (q : X → ℂ → ℂ) (fun x z =>
          ((fun p : Ω => (p : X)) '' A).indicator
            (fun _ : X => (1 : ENNReal)) ((chartAt ℂ x).symm z)) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := R.toRiemannAtlas.isManifold
  let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
  let : MeasurableSpace Ω := borel Ω
  let : BorelSpace Ω := ⟨rfl⟩
  let F : ℝ → Ω → Ω := nativeRootHorizontalTimeMap R q β
  have hact := nativeRootHorizontalTimeMap_action R q β hβ
  have hleft (u : ℝ) (p : Ω) : F (-u) (F u p) = p := by
    calc
      F (-u) (F u p) = F (-u + u) p := (hact.2 (-u) u p).symm
      _ = p := by rw [neg_add_cancel]; exact hact.1 p
  have hright (u : ℝ) (p : Ω) : F u (F (-u) p) = p := by
    simpa only [neg_neg] using hleft (-u) p
  refine ⟨fun t => ?_, ?_⟩
  · exact ((nativeRootHorizontalTimeMap_continuous R q β hβ).comp
      (continuous_const.prodMk continuous_id)).measurable
  intro t A hA
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hcomap : (borel X).comap (Subtype.val : Ω → X) = borel Ω :=
    (borel_comap (f := (Subtype.val : Ω → X))).symm
  have htrace : @MeasurableSet Ω ((borel X).comap (Subtype.val : Ω → X)) A := by
    rw [hcomap]
    exact hA
  obtain ⟨B, hBm, hBA⟩ := MeasurableSpace.measurableSet_comap.1 htrace
  let U : X → ENNReal := B.indicator (fun _ : X => 1)
  let f : X → ENNReal := fun p =>
    if hp : p ∉ s26v_E (q : X → ℂ → ℂ) then U (F (-t) ⟨p, hp⟩ : X) else U p
  have hqfun : (q : X → ℂ → ℂ) ≠ 0 := fun hzero => hq (Subtype.ext hzero)
  have hmemA (p : Ω) : p ∈ A ↔ (p : X) ∈ B := by
    change p ∈ A ↔ p ∈ Subtype.val ⁻¹' B
    rw [hBA]
  have hmemImage (p : Ω) : (p : X) ∈ (Subtype.val : Ω → X) '' (F t '' A) ↔
      (F (-t) p : X) ∈ B := by
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, hr⟩
      have heq : F t s = p := Subtype.ext hr
      have hs' : s = F (-t) p := by
        calc
          s = F (-t) (F t s) := (hleft t s).symm
          _ = F (-t) p := congrArg (F (-t)) heq
      rw [← hs']
      exact (hmemA s).1 hs
    · intro hpB
      refine ⟨F t (F (-t) p), ⟨F (-t) p, (hmemA _).2 hpB, rfl⟩, ?_⟩
      exact congrArg Subtype.val (hright t p)
  have himage : surfaceIntegral (q : X → ℂ → ℂ) (fun x z =>
      ((Subtype.val : Ω → X) '' (F t '' A)).indicator (fun _ : X => (1 : ENNReal))
        ((chartAt ℂ x).symm z)) =
      surfaceIntegral (q : X → ℂ → ℂ) (fun x z => f ((chartAt ℂ x).symm z)) := by
    refine s26v_a_surfaceIntegral_congr_off (q : X → ℂ → ℂ) (s26v_E (q : X → ℂ → ℂ))
      (s26v_E_null q.property hqfun) fun x p hp hpE => ?_
    simp only [(chartAt ℂ x).left_inv hp, f, dite_eq_left hpE]
    have heq := hmemImage ⟨p, hpE⟩
    dsimp only [U]
    by_cases hpB : (F (-t) ⟨p, hpE⟩ : X) ∈ B
    · rw [Set.indicator_of_mem (heq.mpr hpB), Set.indicator_of_mem hpB]
    · rw [Set.indicator_of_notMem (fun h => hpB (heq.mp h)), Set.indicator_of_notMem hpB]
  have hsource : surfaceIntegral (q : X → ℂ → ℂ) (fun x z => U ((chartAt ℂ x).symm z)) =
      surfaceIntegral (q : X → ℂ → ℂ) (fun x z =>
        ((Subtype.val : Ω → X) '' A).indicator (fun _ : X => (1 : ENNReal)) ((chartAt ℂ x).symm z)) := by
    refine s26v_a_surfaceIntegral_congr_off (q : X → ℂ → ℂ) (s26v_E (q : X → ℂ → ℂ))
      (s26v_E_null q.property hqfun) fun x p hp hpE => ?_
    simp only [(chartAt ℂ x).left_inv hp]
    have heq : p ∈ (Subtype.val : Ω → X) '' A ↔ p ∈ B := by
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact (hmemA r).1 hr
      · intro hpB
        exact ⟨⟨p, hpE⟩, (hmemA _).2 hpB, rfl⟩
    dsimp only [U]
    by_cases hpB : p ∈ B
    · rw [Set.indicator_of_mem hpB, Set.indicator_of_mem (heq.mpr hpB)]
    · rw [Set.indicator_of_notMem hpB, Set.indicator_of_notMem (fun h => hpB (heq.mp h))]
  exact himage.trans ((rootTimeMap_integral R q hq β hβ U (indicator_borelInCharts R B hBm) (-t)).trans hsource)

end LowDimensionalTopology.Geometry.Teichmuller
