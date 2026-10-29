/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0), through the
credited uniformization-transport and normalized-lift uniqueness APIs;
see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalFrickeBoundaryNormalization
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalFrickeMatrixConvergence
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexQuotientTopology
public import LowDimensionalTopology.Geometry.Teichmuller.SymmetricSolutionContinuity
public import LowDimensionalTopology.Unproved.Teichmuller.NativeFrickeCoordinateContinuity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Continuity of the original native finite Fricke coordinates

Small distances in the actual quasiconformal metric provide comparisons
between the original marked targets. Their prescribed normalized lifts are
the symmetric normalized solutions with coefficient bounds tending to zero.
The original ordered matrix coordinates therefore converge. Only actual
availability of the prescribed canonical models is an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation LiZhongQC

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
variable {hg : 1 < g} {e : X ≃ₜ PolygonQuotient g}

private theorem firstBookCoordinates_tendsto_of_distance
    {m : MarkedRiemannSurface.{0, 0} R}
    (P : NormalizedCanonicalFuchsianModel hg e m)
    {mn : ℕ → MarkedRiemannSurface.{0, 0} R}
    (Pn : ∀ n, NormalizedCanonicalFuchsianModel hg e (mn n))
    (hdist : Tendsto (fun n => TeichmullerSpace.fromQCDistance R
      (TeichmullerSpace.mk m) (TeichmullerSpace.mk (mn n))) atTop (𝓝 0)) :
    Tendsto (fun n => (Pn n).firstBookCoordinates) atTop (𝓝 P.firstBookCoordinates) := by
  let := m.surface.toRiemannAtlas.toChartedSpace
  let := m.surface.toRiemannAtlas.isManifold
  let := m.surface.t2Space
  let := m.surface.connectedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := P.model.exists_halfPlaneCover_uniformization
  let ε : ℕ → ℝ := fun n => TeichmullerSpace.fromQCDistance R
    (TeichmullerSpace.mk m) (TeichmullerSpace.mk (mn n)) + 1 / ((n : ℝ) + 1)
  have hex (n : ℕ) :
      ∃ (f : m.carrier ≃ₜ (mn n).carrier) (K : ℝ), 1 ≤ K ∧
        (let := (mn n).surface.toRiemannAtlas.toChartedSpace
         IsKQCRS f K) ∧ Real.log K < ε n ∧
        ContinuousMap.Homotopic
          ((_root_.toContinuousMap f).comp m.markingMap) (mn n).markingMap := by
    apply m.exists_quasiconformal_map_of_distance_lt (mn n)
    change TeichmullerSpace.fromQCDistance R
      (TeichmullerSpace.mk m) (TeichmullerSpace.mk (mn n)) <
        TeichmullerSpace.fromQCDistance R
          (TeichmullerSpace.mk m) (TeichmullerSpace.mk (mn n)) + 1 / ((n : ℝ) + 1)
    exact lt_add_of_pos_right _ (by positivity)
  choose f K hK hQC hlog hhom using hex
  have hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    simpa only [add_zero] using hdist.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hlogzero : Tendsto (fun n => Real.log (K n)) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => Real.log_nonneg (hK n)) (fun n => (hlog n).le) hεzero
  have hexplog (n : ℕ) : Real.exp (Real.log (K n)) = K n :=
    Real.exp_log (by linarith [hK n])
  have hKzero : Tendsto K atTop (𝓝 (1 : ℝ)) :=
    (Real.tendsto_exp_nhds_zero_nhds_one.comp hlogzero).congr hexplog
  let k : ℕ → ℝ := fun n => (K n - 1) / (K n + 1)
  have hk₀ (n : ℕ) : 0 ≤ k n :=
    div_nonneg (by linarith [hK n]) (by linarith [hK n])
  have hk (n : ℕ) : k n < 1 := by
    change (K n - 1) / (K n + 1) < 1
    apply (div_lt_one (by linarith [hK n])).2
    linarith
  have hkzero : Tendsto k atTop (𝓝 (0 : ℝ)) := by
    have hdiv : Tendsto ((fun n => K n - 1) / (fun n => K n + 1))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, one_add_one_eq_two, zero_div] using
        (hKzero.sub_const 1).div (hKzero.add_const 1) (by norm_num)
    exact hdiv.congr (fun _ => rfl)
  have hLift (n : ℕ) :
      let := (mn n).surface.toRiemannAtlas.toChartedSpace
      ∃ (B : ℍ ≃ₜ ℍ) (G : ExtPlane → ExtPlane),
        IsNormalizedLift P.model.halfPlaneCover (Pn n).model.halfPlaneCover (f n) B G ∧
        IsKQC (liftToC B) upperHalf (K n) ∧
        ∀ (d : Edge g) (z : ℍ), B (P.matrices d • z) = (Pn n).matrices d • B z := by
    let := (mn n).surface.toRiemannAtlas.toChartedSpace
    dsimp only
    exact P.exists_normalized_comparison_lift (Pn n) (f n) (hQC n) (hhom n)
  choose B G hnorm _hBK hintertwine using hLift
  let μ : ℕ → ℂ → ℂ := fun n =>
    let := (mn n).surface.toRiemannAtlas.toChartedSpace
    s27u_liftCoeff P.model.halfPlaneCover (f n)
  have hμ (n : ℕ) : IsBeltramiCoeff (μ n) upperHalf (k n) := by
    let := (mn n).surface.toRiemannAtlas.toChartedSpace
    let := (mn n).surface.toRiemannAtlas.isManifold
    exact s27u_liftCoeff_isBeltramiCoeff hp (hQC n)
  have hsym (n : ℕ) (z : ℍ) : (B n z : ℂ) = s27u_fSym (μ n) z := by
    let := (mn n).surface.toRiemannAtlas.toChartedSpace
    let := (mn n).surface.toRiemannAtlas.isManifold
    let := (mn n).surface.t2Space
    let := (mn n).surface.connectedSpace
    obtain ⟨Γn, _hΓn, hpn⟩ := (Pn n).model.exists_halfPlaneCover_uniformization
    obtain ⟨F, hF, hpF, hNF, _hreal, _hdil⟩ :=
      s27u_uniformization_transport hp (f n) ⟨K n, hQC n⟩
    have hBF : B n = F :=
      (normalizedLift_unique hp hpn hpF (f n) (hnorm n) hNF).1
    rw [hBF]
    exact hF z
  have hloc := symmetricSolution_tendstoLocallyUniformly_zero μ k hk₀ hk hμ hkzero
  have hconv (z : ℍ) : Tendsto (fun n => B n z) atTop (𝓝 z) := by
    apply UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff.mpr
    have hz := hloc.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (z : ℂ))
    exact hz.congr (fun n => (hsym n z).symm)
  exact P.firstBookCoordinates_tendsto_of_intertwining Pn hconv hintertwine

private theorem continuous_flatten_original_book_data :
    Continuous (flattenFirstBookData (g := g)) := by
  apply continuous_pi
  intro j
  let p := (bookIndexEquiv g).symm j
  change Continuous (fun v : FirstBookData g => sixBookEntries (v p.1) p.2)
  have hentry (k : Fin 6) :
      Continuous (fun v : FirstBookData g => sixBookEntries (v p.1) k) := by
    fin_cases k <;> dsimp only [sixBookEntries] <;> fun_prop
  exact hentry p.2

/-- The actual finite ordered Fricke coordinates are continuous for the
original quasiconformal metric, using only prescribed-model availability. -/
theorem nativeFrickeCoordinateContinuity
    (R : ClosedRiemannSurface X) (hg : 1 < g) (hgenus : R.HasGenus g)
    (e : X ≃ₜ PolygonQuotient g)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e) :
    LowDimensionalTopology.Unproved.Teichmuller.NativeFrickeCoordinateContinuity R hg hgenus e hA := by
  unfold Unproved.Teichmuller.NativeFrickeCoordinateContinuity
  let mT : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.qcMetricSpace R hg hgenus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} R) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  change Continuous (finiteFrickeCoordinates hA)
  apply continuous_iff_seqContinuous.mpr
  intro u q hu
  obtain ⟨m, rfl⟩ := Quotient.exists_rep q
  have hreps (n : ℕ) : ∃ mn : MarkedRiemannSurface.{0, 0} R,
      TeichmullerSpace.mk mn = u n := Quotient.exists_rep (u n)
  choose mn hmn using hreps
  let P := chosenCanonicalModel hA m
  let Pn := fun n => chosenCanonicalModel hA (mn n)
  have hdist : Tendsto (fun n => TeichmullerSpace.fromQCDistance R
      (TeichmullerSpace.mk m) (TeichmullerSpace.mk (mn n))) atTop (𝓝 0) := by
    have hzero : Tendsto (fun n => dist (u n) (TeichmullerSpace.mk m))
        atTop (𝓝 (0 : ℝ)) := tendsto_iff_dist_tendsto_zero.mp hu
    apply hzero.congr
    intro n
    calc
      dist (u n) (TeichmullerSpace.mk m) =
          dist (TeichmullerSpace.mk m) (u n) := dist_comm _ _
      _ = TeichmullerSpace.fromQCDistance R (TeichmullerSpace.mk m) (u n) :=
        TeichmullerSpace.qcMetricSpace_dist R hg hgenus (TeichmullerSpace.mk m) (u n)
      _ = TeichmullerSpace.fromQCDistance R
          (TeichmullerSpace.mk m) (TeichmullerSpace.mk (mn n)) :=
        congrArg (TeichmullerSpace.fromQCDistance R (TeichmullerSpace.mk m)) (hmn n).symm
  have hcoords := firstBookCoordinates_tendsto_of_distance P Pn hdist
  have hflat := (continuous_flatten_original_book_data.tendsto P.firstBookCoordinates).comp
    hcoords
  change Tendsto (fun n => finiteFrickeCoordinates hA (u n)) atTop
    (𝓝 (flattenFirstBookData P.firstBookCoordinates))
  apply hflat.congr
  intro n
  exact congrArg (finiteFrickeCoordinates hA) (hmn n)

end LowDimensionalTopology.Geometry.Teichmuller
