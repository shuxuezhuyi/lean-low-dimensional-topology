module

public import LowDimensionalTopology.Geometry.Teichmuller.ConditionalInvariantStraightLine
public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerClassification
public import Mathlib.Tactic.Convert

/-!
# Absolute extremality of an actual map and its square

The original complex structure, self-homeomorphism and its actual square are
retained. The straight-line input concerns the genuine full-log marked metric.
All competing positive structures and actual homotopic maps remain in the
joint extremal problem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The unchanged original complex structure, with its genuine smooth identity. -/
def PositiveComplexStructure.refl : PositiveComplexStructure R where
  surface := R
  identity := SmoothSurfaceEquiv.refl R.toRiemannSurface
  identity_map := rfl
  orientation_preserving := preservesComplexOrientation_id R.toRiemannAtlas

local notation "AutR" =>
  @SourceQCModular.Aut X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold
local notation "QCPointR" => @TeichSpace X _ R.toRiemannAtlas.toChartedSpace

private theorem minimizingPoint_iff_displacement_sq_eq_two_mul
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hgeometry : OriginalTeichmullerStraightLineGeometry R hg hgenus)
    (γ : ModularR) (p : QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
    IsMinimizingPoint R γ p ↔ dist p (γ ^ 2 • p) = 2 * dist p (γ • p) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  have hiso (δ : ModularR) : Isometry (fun q : QCPointR => δ • q) :=
    SourceQCModular.bookMetric_isometry hg (R.hasSourceGenus hgenus) δ
  constructor
  · intro hp
    by_cases hzero : dist p (γ • p) = 0
    · have hfix : γ • p = p := (dist_eq_zero.mp hzero).symm
      simp only [pow_two, mul_smul, hfix, dist_self, mul_zero]
    · have hpos : 0 < dist p (γ • p) := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
      obtain ⟨ℓ, hℓ, hpℓ, hinvariant⟩ :=
        exists_invariantLine_of_minimizingPoint_of_pos R hg hgenus hgeometry γ p hp hpos
      rcases invariantLine_reflection_or_orbit_minimum
          R hg hgenus γ p ℓ hℓ hpℓ hinvariant with ⟨c, hc⟩ | ⟨horbit, _⟩
      · have hfix : γ • ℓ (c / 2) = ℓ (c / 2) := by
          rw [hc]
          congr 1
          ring
        have hbound := (isMinimizingPoint_iff R γ p).mp hp (ℓ (c / 2))
        change dist p (γ • p) ≤ dist (ℓ (c / 2)) (γ • ℓ (c / 2)) at hbound
        rw [hfix, dist_self] at hbound
        exact False.elim ((not_le_of_gt hpos) hbound)
      · simpa using horbit 2
  · intro hdouble
    by_cases hzero : dist p (γ • p) = 0
    · apply (isMinimizingPoint_iff R γ p).mpr
      intro q
      change dist p (γ • p) ≤ dist q (γ • q)
      rw [hzero]
      exact dist_nonneg
    · have hpos : 0 < dist p (γ • p) := lt_of_le_of_ne dist_nonneg (Ne.symm hzero)
      have hpne : p ≠ γ ^ 2 • p := by
        apply dist_pos.mp
        rw [hdouble]
        linarith
      obtain ⟨hline, hunique, hbetween⟩ := hgeometry
      obtain ⟨ℓ, hℓ, hstart, hend⟩ := hline p (γ ^ 2 • p) hpne
      have hstep : dist (γ • p) (γ ^ 2 • p) = dist p (γ • p) := by
        rw [pow_two, mul_smul, (hiso γ).dist_eq]
      have hmid : γ • p ∈ range ℓ := by
        apply hbetween ℓ hℓ 0 (dist p (γ ^ 2 • p)) (γ • p)
        rw [hstart, hend, hstep, hdouble]
        ring
      have hpℓ : p ∈ range ℓ := ⟨0, hstart⟩
      have hlast : γ ^ 2 • p ∈ range ℓ := ⟨dist p (γ ^ 2 • p), hend⟩
      have hγℓ : Isometry (fun t : ℝ => γ • ℓ t) := (hiso γ).comp hℓ
      have hranges : range (fun t : ℝ => γ • ℓ t) = range ℓ := by
        apply hunique _ ℓ hγℓ hℓ (γ • p) (γ ^ 2 • p)
        · apply dist_pos.mp
          rw [hstep]
          exact hpos
        · exact ⟨0, congrArg (fun q : QCPointR => γ • q) hstart⟩
        · obtain ⟨r, hr⟩ := hmid
          refine ⟨r, ?_⟩
          change γ • ℓ r = γ ^ 2 • p
          rw [hr, pow_two, mul_smul]
        · exact hmid
        · exact hlast
      have hinvariant : (fun q : QCPointR => γ • q) '' range ℓ = range ℓ := by
        simpa only [range_comp'] using hranges
      rcases invariantLine_reflection_or_orbit_minimum
          R hg hgenus γ p ℓ hℓ hpℓ hinvariant with ⟨c, hc⟩ | ⟨_, hp⟩
      · obtain ⟨r, hr⟩ := hpℓ
        have hsqfix : γ ^ 2 • p = p := by
          rw [← hr, pow_two, mul_smul, hc, hc]
          congr 1
          ring
        exact False.elim (hpne hsqfix.symm)
      · exact hp

private theorem extremal_of_absolutelyExtremal_refl
    (f h : X ≃ₜ X)
    (habsolute : IsAbsolutelyExtremal R f (PositiveComplexStructure.refl R) h) :
    letI := R.toRiemannAtlas.toChartedSpace
    IsExtremalInHomotopyClass h := by
  let := R.toRiemannAtlas.toChartedSpace
  refine ⟨habsolute.1, ?_⟩
  intro k hk hhom
  have hbound := habsolute.2.2 (PositiveComplexStructure.refl R) k
    (hhom.symm.trans habsolute.2.1)
  have hkOriginal : (PositiveComplexStructure.refl R).IsQC k := hk
  simp only [PositiveComplexStructure.dilatation, habsolute.1, hkOriginal, ↓reduceIte] at hbound
  simp only [PositiveComplexStructure.nativeDilatation] at hbound
  convert! hbound using 1

private theorem bookTeichmuller_of_extremal
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (f : X ≃ₜ X)
    (hext : letI := R.toRiemannAtlas.toChartedSpace
      IsExtremalInHomotopyClass f) : IsBookTeichmullerMap R R f := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨f₀, _hhom, hkind, _hext, huniq⟩ :=
    R.exists_unique_teichmuller_extremal R hg hgenus f hext.1
  have heq : f = f₀ := huniq f hext (ContinuousMap.Homotopic.refl _)
  rw [heq]
  exact (isBookTeichmullerMap_iff_geometric R R f₀).mpr hkind

private theorem absolutelyExtremal_of_extremal_and_minimal_refl
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (f : X ≃ₜ X)
    (hext : letI := R.toRiemannAtlas.toChartedSpace
      IsExtremalInHomotopyClass f)
    (hminimal : IsMinimalComplexStructure R f (PositiveComplexStructure.refl R)) :
    IsAbsolutelyExtremal R f (PositiveComplexStructure.refl R) f := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨h, habsolute⟩ := hminimal
  have hhext := extremal_of_absolutelyExtremal_refl R f h habsolute
  obtain ⟨f₀, _hhom, _hkind, _hext, huniq⟩ :=
    R.exists_unique_teichmuller_extremal R hg hgenus f hext.1
  have hf₀ : f = f₀ := huniq f hext (ContinuousMap.Homotopic.refl _)
  have hh₀ : h = f₀ := huniq h hhext habsolute.2.1.symm
  have heq : h = f := hh₀.trans hf₀.symm
  simpa only [heq] using habsolute

private theorem displacement_eq_log_of_extremal_refl
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (f : X ≃ₜ X)
    (hext : letI := R.toRiemannAtlas.toChartedSpace
      IsExtremalInHomotopyClass f)
    (a : AutR)
    (hfa : ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap a.val)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    displacement R (SourceQCModular.mk a) (PositiveComplexStructure.refl R).point =
      Real.log (maxDilatationRS f).toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.connectedSpace
  have hupper := displacement_le_log R (PositiveComplexStructure.refl R) hext.1 hfa
  obtain ⟨h, hqc, hhom, hlog⟩ :=
    displacement_attained R hg hgenus a (PositiveComplexStructure.refl R)
  have hbound : maxDilatationRS f ≤ maxDilatationRS h :=
    hext.2 h hqc (hfa.trans hhom.symm)
  have hpos : 0 < (maxDilatationRS f).toReal :=
    zero_lt_one.trans_le (s29_m_one_le_toReal hext.1)
  have hlogle : Real.log (maxDilatationRS f).toReal ≤
      Real.log (maxDilatationRS h).toReal :=
    Real.log_le_log hpos (ENNReal.toReal_mono (s29_m_maxDilatationRS_ne_top hqc) hbound)
  apply le_antisymm hupper
  rw [hlog]
  exact hlogle

/-- An actual original positive self-homeomorphism is absolutely extremal
exactly in the conformal or literal Teichmüller-square cases. -/
theorem absolutelyExtremal_iff_conformal_or_teichmuller_square
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hgeometry : OriginalTeichmullerStraightLineGeometry R hg hgenus)
    (f : X ≃ₜ X)
    (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      IsOrientationPreservingRS f) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    IsAbsolutelyExtremal R f (PositiveComplexStructure.refl R) f ↔
      RiemannAnalyticMap R.toRiemannAtlas R.toRiemannAtlas f ∨
        (IsBookTeichmullerMap R R f ∧
          IsBookTeichmullerMap R R (f.trans f) ∧
          maxDilatationRS (f.trans f) = maxDilatationRS f ^ 2) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
  let σ₀ := PositiveComplexStructure.refl R
  obtain ⟨a, ha, hcomparison, _hexists⟩ :=
    originalHomeomorph_minimizer_comparison R hg hgenus f hf
  have hfa : ContinuousMap.Homotopic (_root_.toContinuousMap f)
      (_root_.toContinuousMap a.val) := by
    simpa only [SourceQCModular.continuousMap] using ha
  have hfasq : ContinuousMap.Homotopic (_root_.toContinuousMap (f.trans f))
      (_root_.toContinuousMap (a * a).val) := hfa.comp hfa
  have hclass : SourceQCModular.mk (a * a) = SourceQCModular.mk a ^ 2 := by
    rw [pow_two]
    rfl
  constructor
  · intro habsolute
    have hext := extremal_of_absolutelyExtremal_refl R f f habsolute
    have hbook := bookTeichmuller_of_extremal R hg hgenus f hext
    have hp : IsMinimizingPoint R (SourceQCModular.mk a) σ₀.point :=
      (hcomparison σ₀).mp ⟨f, habsolute⟩
    have hdouble :=
      (minimizingPoint_iff_displacement_sq_eq_two_mul
        R hg hgenus hgeometry (SourceQCModular.mk a) σ₀.point).mp hp
    have hdist := displacement_eq_log_of_extremal_refl R hg hgenus f hext a hfa
    have hsqQC : IsQCRS (f.trans f) := s28q_isQCRS_trans hext.1 hext.1
    obtain ⟨h, hhom, hkind, hhext, _huniq⟩ :=
      R.exists_unique_teichmuller_extremal R hg hgenus (f.trans f) hsqQC
    have hdistSq := displacement_eq_log_of_extremal_refl R hg hgenus h hhext
      (a * a) (hhom.symm.trans hfasq)
    have hlogs : Real.log (maxDilatationRS h).toReal =
        2 * Real.log (maxDilatationRS f).toReal := by
      calc
        Real.log (maxDilatationRS h).toReal =
            displacement R (SourceQCModular.mk (a * a)) σ₀.point := hdistSq.symm
        _ = dist σ₀.point (SourceQCModular.mk a ^ 2 • σ₀.point) := by
          rw [hclass]
          rfl
        _ = 2 * dist σ₀.point (SourceQCModular.mk a • σ₀.point) := hdouble
        _ = 2 * Real.log (maxDilatationRS f).toReal := by
          change 2 * displacement R (SourceQCModular.mk a) σ₀.point = _
          rw [hdist]
    have hfpos : 0 < (maxDilatationRS f).toReal :=
      zero_lt_one.trans_le (s29_m_one_le_toReal hext.1)
    have hhpos : 0 < (maxDilatationRS h).toReal :=
      zero_lt_one.trans_le (s29_m_one_le_toReal hhext.1)
    have hKpow : maxDilatationRS h = maxDilatationRS f ^ 2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (s29_m_maxDilatationRS_ne_top hhext.1)
        (ENNReal.pow_ne_top (s29_m_maxDilatationRS_ne_top hext.1))).mp
      rw [ENNReal.toReal_pow]
      apply Real.log_injOn_pos hhpos (pow_pos hfpos 2)
      rw [Real.log_pow]
      exact hlogs
    have hupper : maxDilatationRS (f.trans f) ≤ maxDilatationRS f ^ 2 := by
      have hff : (f.trans f : X → X) = (f : X → X) ∘ f := by
        funext x
        rfl
      rw [hff, pow_two]
      exact (eq23_4 (s29_m_isKQCRS_maxDil hext.1) (s29_m_isKQCRS_maxDil hext.1)).2
    have hlower := hhext.2 (f.trans f) hsqQC hhom.symm
    rw [hKpow] at hlower
    have hKsq : maxDilatationRS (f.trans f) = maxDilatationRS f ^ 2 :=
      le_antisymm hupper hlower
    have heq : f.trans f = h :=
      ((R.teichmullerMap_unique_extremal R hg hgenus hkind).2
        (f.trans f) hsqQC hhom.symm).2.mp (hKsq.trans hKpow.symm)
    have hbookSq : IsBookTeichmullerMap R R (f.trans f) := by
      rw [heq]
      exact (isBookTeichmullerMap_iff_geometric R R h).mpr hkind
    exact Or.inr ⟨hbook, hbookSq, hKsq⟩
  · rintro (hanalytic | ⟨hbook, hbookSq, hKsq⟩)
    · have hbihol :=
        (analyticHomeomorph_iff_sourceBiholomorphic R.toRiemannAtlas R.toRiemannAtlas f).mp
          hanalytic
      have hfOne := (isKQCRS_one_iff f).mpr hbihol
      have hfQC : IsQCRS f := ⟨1, hfOne⟩
      have hKone : maxDilatationRS f = 1 :=
        le_antisymm (by simpa using maxDilatationRS_le hfOne)
          (s29_m_one_le_maxDilatationRS hfQC)
      have hfOriginal : (PositiveComplexStructure.refl R).IsQC f := hfQC
      have hleft : (PositiveComplexStructure.refl R).dilatation f = 1 := by
        simp only [PositiveComplexStructure.dilatation, hfOriginal, ↓reduceIte]
        simp only [PositiveComplexStructure.nativeDilatation]
        convert! hKone using 1
      refine ⟨hfQC, ContinuousMap.Homotopic.refl _, ?_⟩
      intro τ k _hhom
      rw [hleft]
      by_cases hk : τ.IsQC k
      · rw [PositiveComplexStructure.dilatation, ite_eq_left hk,
          ← ENNReal.ofReal_toReal (τ.nativeDilatation_ne_top k hk), ENNReal.one_le_ofReal]
        exact τ.one_le_nativeDilatation_toReal k hk
      · simp only [PositiveComplexStructure.dilatation, hk, ↓reduceIte, le_top]
    · have hext := (R.teichmullerMap_unique_extremal R hg hgenus
        ((isBookTeichmullerMap_iff_geometric R R f).mp hbook)).1
      have hextSq := (R.teichmullerMap_unique_extremal R hg hgenus
        ((isBookTeichmullerMap_iff_geometric R R (f.trans f)).mp hbookSq)).1
      have hdist := displacement_eq_log_of_extremal_refl R hg hgenus f hext a hfa
      have hdistSq := displacement_eq_log_of_extremal_refl R hg hgenus
        (f.trans f) hextSq (a * a) hfasq
      have hlogs : Real.log (maxDilatationRS (f.trans f)).toReal =
          2 * Real.log (maxDilatationRS f).toReal := by
        simpa [ENNReal.toReal_pow, Real.log_pow] using
          congrArg (fun k : ℝ≥0∞ => Real.log k.toReal) hKsq
      have hdouble : dist σ₀.point (SourceQCModular.mk a ^ 2 • σ₀.point) =
          2 * dist σ₀.point (SourceQCModular.mk a • σ₀.point) := by
        change displacement R (SourceQCModular.mk a ^ 2) σ₀.point =
          2 * displacement R (SourceQCModular.mk a) σ₀.point
        rw [← hclass, hdistSq, hdist]
        exact hlogs
      have hp := (minimizingPoint_iff_displacement_sq_eq_two_mul
        R hg hgenus hgeometry (SourceQCModular.mk a) σ₀.point).mpr hdouble
      exact absolutelyExtremal_of_extremal_and_minimal_refl R hg hgenus f hext
        ((hcomparison σ₀).mpr hp)

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
