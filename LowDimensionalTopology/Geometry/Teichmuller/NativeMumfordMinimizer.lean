module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeQCModularComparison
public import LowDimensionalTopology.Geometry.Teichmuller.NativeModularProperAction
public import LowDimensionalTopology.Geometry.Teichmuller.NativeModularDisplacementTypes
public import LowDimensionalTopology.Unproved.Teichmuller.NativeMumfordSequentialCompactness
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# The Mumford and finite-ball endgame for an actual minimizing sequence

Uniform thickness is tested on every actual essential simple free class.
The explicit existing Mumford input gives convergence after actual native
mapping classes. The full-QC finite-ball theorem gives a constant conjugate
subsequence; continuity then gives an actual minimizing point after applying
the inverse of one of the original native mapping classes.

This file does not supply irreducibility-to-thickness or prove Mumford.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC

variable {X : Type} [TopologicalSpace X]
variable (R : ClosedRiemannSurface X)

local notation "QCPointR" => @TeichSpace X _ R.toRiemannAtlas.toChartedSpace
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace
    R.toRiemannAtlas.isManifold

private theorem exists_strictMono_constant_conjugates_of_tendsto
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (γ : ModularR) (χ : ℕ → ModularR) (q : ℕ → QCPointR) (a : QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    letI := R.t2Space
    letI := R.connectedSpace
    letI := R.compactSpace
    letI := QCBookMetric.metricSpace hg (R.hasSourceGenus hgenus)
    Tendsto q atTop (𝓝 a) →
      (∃ B : ℝ, ∀ᶠ n in atTop,
        QCBookMetric.bookDistance (q n) ((χ n * γ * (χ n)⁻¹) • q n) < B) →
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n,
        χ (σ n) * γ * (χ (σ n))⁻¹ = χ (σ 0) * γ * (χ (σ 0))⁻¹ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let hR := R.hasSourceGenus hgenus
  let := QCBookMetric.metricSpace hg hR
  intro hq hbound
  obtain ⟨B, hB⟩ := hbound
  let G (n : ℕ) : ModularR := χ n * γ * (χ n)⁻¹
  change ∀ᶠ n in atTop, QCBookMetric.bookDistance (q n) (G n • q n) < B at hB
  obtain ⟨j, hj⟩ := hB.exists
  have hBpos : 0 < B :=
    lt_of_le_of_lt (dist_nonneg : 0 ≤ dist (q j) (G j • q j)) hj
  have hnear : ∀ᶠ n in atTop, dist (q n) a < 1 :=
    hq.eventually (Metric.ball_mem_nhds a (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hnear.and hB)
  obtain ⟨Γ, p, _hΓ, _hfree, hp⟩ := s22hg_exists_fuchsian_uniformization hg hR
  let S : Set (ModularR) :=
    {δ | ∃ z : QCPointR,
      teichDistance a z < B + 2 ∧ teichDistance a (δ • z) < B + 2}
  have hS : S.Finite := SourceQCModular.finite_ball_transporter hg hR hp a (B + 2)
  have hmem (n : ℕ) : G (N + n) ∈ S := by
    obtain ⟨hn, hbn⟩ := hN (N + n) (Nat.le_add_right N n)
    have hqa : QCBookMetric.bookDistance a (q (N + n)) < 1 := by
      change dist a (q (N + n)) < 1
      rw [dist_comm]
      exact hn
    have htri := dist_triangle a (q (N + n)) (G (N + n) • q (N + n))
    change QCBookMetric.bookDistance a (G (N + n) • q (N + n)) ≤
      QCBookMetric.bookDistance a (q (N + n)) +
        QCBookMetric.bookDistance (q (N + n)) (G (N + n) • q (N + n)) at htri
    have hfull : QCBookMetric.bookDistance a (G (N + n) • q (N + n)) < B + 1 := by
      linarith
    have hhalf₁ := QCBookMetric.bookDistance_eq_two_mul a (q (N + n))
    have hhalf₂ := QCBookMetric.bookDistance_eq_two_mul a (G (N + n) • q (N + n))
    exact ⟨q (N + n), by linarith, by linarith⟩
  let F : ℕ → S := fun n => ⟨G (N + n), hmem n⟩
  let : Finite S := Set.finite_coe_iff.mpr hS
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber F
  have hcInfinite : {n : ℕ | F n = c}.Infinite := Set.infinite_coe_iff.mp hc
  obtain ⟨ρ, hρ, hρc⟩ := Nat.exists_strictMono_subsequence (fun K => by
    obtain ⟨n, hn, hKn⟩ := hcInfinite.exists_gt K
    exact ⟨n, hKn, hn⟩)
  refine ⟨fun n => N + ρ n, fun i k hik => Nat.add_lt_add_left (hρ hik) N, ?_⟩
  intro n
  exact (congrArg Subtype.val (hρc n)).trans (congrArg Subtype.val (hρc 0)).symm

/-- A uniformly thick actual native minimizing sequence attains its original
full-QC displacement infimum, conditional on the explicit existing Mumford input. -/
theorem exists_native_minimizingPoint_of_mumford_and_thick_minimizing_sequence
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hMumford : LowDimensionalTopology.Unproved.Teichmuller.NativeMumfordSequentialCompactness
      R hg hgenus)
    (γ : ModularR) (points : ℕ → TeichmullerSpace.{0, 0} R)
    (hthick : ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (c : EssentialSimpleFreeClass X),
      δ < (markedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus (points n) c : ℝ)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    Tendsto (fun n => displacement R γ (TeichmullerSpace.toSource R (points n)))
        atTop (𝓝 (infimalDisplacement R γ)) →
      ∃ p : TeichmullerSpace.{0, 0} R,
        IsMinimizingPoint R γ (TeichmullerSpace.toSource R p) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let hR := R.hasSourceGenus hgenus
  let := QCBookMetric.metricSpace hg hR
  let mNative := TeichmullerSpace.fromQCMetricSpace R hg hgenus
    (canonicalHandleGroupPresentation g)
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mNative.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : MetricSpace (TeichmullerSpace.{0, 0} R) := mNative
  intro hlim
  obtain ⟨σ, hσ, χ, q, hq⟩ := hMumford points hthick
  have htoSource : Isometry (TeichmullerSpace.toSource R) := by
    apply Isometry.of_dist_eq
    intro p q
    rfl
  let qn (n : ℕ) : QCPointR :=
    TeichmullerSpace.toSource R (χ n • points (σ n))
  let cn (n : ℕ) : ModularR := MappingClassGroup.toQCModular R (χ n)
  have hqSource : Tendsto qn atTop (𝓝 (TeichmullerSpace.toSource R q)) :=
    (htoSource.continuous.tendsto q).comp hq
  have hlimσ := hlim.comp hσ.tendsto_atTop
  have hbounded : ∃ B : ℝ, ∀ᶠ n in atTop,
      QCBookMetric.bookDistance (qn n) ((cn n * γ * (cn n)⁻¹) • qn n) < B := by
    refine ⟨infimalDisplacement R γ + 1, ?_⟩
    have hsmall := hlimσ.eventually (gt_mem_nhds (lt_add_one (infimalDisplacement R γ)))
    filter_upwards [hsmall] with n hn
    change QCBookMetric.bookDistance
      (TeichmullerSpace.toSource R (χ n • points (σ n)))
      ((MappingClassGroup.toQCModular R (χ n) * γ *
          (MappingClassGroup.toQCModular R (χ n))⁻¹) •
        TeichmullerSpace.toSource R (χ n • points (σ n))) < _
    rw [TeichmullerSpace.bookDistance_conjugate_toSource_smul]
    exact hn
  obtain ⟨τ, hτ, hconst⟩ := exists_strictMono_constant_conjugates_of_tendsto
    R hg hgenus γ cn qn (TeichmullerSpace.toSource R q) hqSource hbounded
  let A : ModularR := cn (τ 0) * γ * (cn (τ 0))⁻¹
  have hqτ := hqSource.comp hτ.tendsto_atTop
  have hA : Isometry (fun z : QCPointR => A • z) :=
    SourceQCModular.bookMetric_isometry hg hR A
  have hAτ := (hA.continuous.tendsto (TeichmullerSpace.toSource R q)).comp hqτ
  have hlimDistance := hqτ.dist hAτ
  have hfunctions :
      (fun n => QCBookMetric.bookDistance (qn (τ n)) (A • qn (τ n))) =
        (fun n => displacement R γ (TeichmullerSpace.toSource R (points (σ (τ n))))) := by
    funext n
    change QCBookMetric.bookDistance (qn (τ n))
      ((cn (τ 0) * γ * (cn (τ 0))⁻¹) • qn (τ n)) = _
    rw [← hconst n]
    exact TeichmullerSpace.bookDistance_conjugate_toSource_smul R (χ (τ n))
      (points (σ (τ n))) γ
  have hlimConst : Tendsto
      (fun n => QCBookMetric.bookDistance (qn (τ n)) (A • qn (τ n)))
      atTop (𝓝 (infimalDisplacement R γ)) := by
    rw [hfunctions]
    exact hlim.comp (hσ.comp hτ).tendsto_atTop
  have hinf : infimalDisplacement R γ =
      QCBookMetric.bookDistance (TeichmullerSpace.toSource R q)
        (A • TeichmullerSpace.toSource R q) :=
    tendsto_nhds_unique hlimConst hlimDistance
  let c := χ (τ 0)
  let p0 : TeichmullerSpace.{0, 0} R := c⁻¹ • q
  have hc : c • p0 = q := smul_inv_smul c q
  have hlast :
      QCBookMetric.bookDistance (TeichmullerSpace.toSource R q)
          (A • TeichmullerSpace.toSource R q) =
        displacement R γ (TeichmullerSpace.toSource R p0) := by
    have hbook := TeichmullerSpace.bookDistance_conjugate_toSource_smul R c p0 γ
    rw [hc] at hbook
    exact hbook
  exact ⟨p0, hinf.trans hlast⟩

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
