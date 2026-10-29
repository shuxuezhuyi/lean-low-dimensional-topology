/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCCoefficientLimit
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Completeness of the original general QC Teichmüller metric

The original reference is uniformized in the book's given fixed-triple
coordinates. Targets retain their independent universe and actual native
atlases. Actual marking-induced atlas transport preserves the original full
log distance. A common-universe limit is transported onto an actual target
carrier of the original sequence, proving completeness of that same original
space. No compactness, genus or controlled representatives are assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open LiZhongQC
universe u v

/-- Transport each original native target along its actual marking, as in the
proved source-carrier construction, then pass to the original quotient. -/
def sourceCarrierMap (R : Surface.{u}) : Space.{u, v} R → Space.{u, u} R :=
  Quotient.lift (fun m => mk m.sourceCarrierRepresentative)
    (fun m n h => Quotient.sound
      ((marked_equivalent_iff_sourceCarrierRepresentatives m n).mp h))

@[simp] theorem sourceCarrierMap_mk {R : Surface.{u}} (m : Marked.{u, v} R) :
    sourceCarrierMap R (mk m) = mk m.sourceCarrierRepresentative := rfl

/-- This is the same original full-log distance across the actual native
target identifications, not an auxiliary coefficient distance. -/
theorem sourceCarrierMap_distance {R : Surface.{u}} (a b : Space.{u, v} R) :
    distance (sourceCarrierMap R a) (sourceCarrierMap R b) = distance a b := by
  refine Quotient.inductionOn₂ a b fun m n => ?_
  exact (distance_eq_sourceCarrierRepresentatives m n).symm

/-- Any actual original marking supplies an actual target carrier on which
every common-universe limit atlas can be transported. No cardinality choice
or extra universe identification is supplied. -/
theorem sourceCarrierMap_surjective_of_marked
    {R : Surface.{u}} (m₀ : Marked.{u, v} R) :
    Function.Surjective (sourceCarrierMap.{u, v} R) := by
  intro a
  obtain ⟨n, rfl⟩ := Quotient.exists_rep a
  let e : ULift.{0, v} m₀.target.carrier ≃ₜ n.target.carrier :=
    (Homeomorph.ulift : ULift.{0, v} m₀.target.carrier ≃ₜ m₀.target.carrier).trans
      (m₀.marking.symm.trans n.marking)
  let S : Surface.{v} := n.target.pullbackHomeomorph e
  let : ChartedSpace ℂ (ULift.{0, v} m₀.target.carrier) := S.riemann.toRiemannAtlas.toChartedSpace
  let : IsManifold 𝓘(ℂ) ω (ULift.{0, v} m₀.target.carrier) := S.riemann.toRiemannAtlas.isManifold
  have he : IsBiholomorphic (e : S.carrier → n.target.carrier) :=
    (analyticHomeomorph_iff_sourceBiholomorphic
      S.riemann.toRiemannAtlas n.target.riemann.toRiemannAtlas e).mp
      (n.target.pullbackHomeomorph_analytic e)
  let m : Marked.{u, v} R :=
    { target := S
      marking := n.marking.trans e.symm
      qc := s28q_isQCRS_trans n.qc
        ⟨1, (isKQCRS_one_iff e.symm).mpr he.homeomorph_symm⟩ }
  refine ⟨mk m, Quotient.sound ?_⟩
  refine ⟨m.sourceCarrierProjection.trans e,
    he.comp m.sourceCarrierProjection_biholomorphic, ?_⟩
  have hh :
      ((m.sourceCarrierRepresentative.marking.trans (m.sourceCarrierProjection.trans e) :
        R.carrier ≃ₜ n.target.carrier) : C(R.carrier, n.target.carrier)) =
        (n.marking : C(R.carrier, n.target.carrier)) := by
    ext x
    change e (m.sourceCarrierProjection
      (m.sourceCarrierProjection.symm (m.marking x))) = n.marking x
    rw [m.sourceCarrierProjection.apply_symm_apply]
    exact e.apply_symm_apply (n.marking x)
  rw [hh]

variable (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
  {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
  (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
    ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)

include hp hfixed in
/-- The actual target transport is an isometry for the original full-log
metrics, including independently sized original native targets. -/
theorem sourceCarrierMap_isometry :
    letI := metricSpace.{u, v} R hp hfixed
    letI := metricSpace.{u, u} R hp hfixed
    Isometry (sourceCarrierMap.{u, v} R) := by
  let := metricSpace.{u, v} R hp hfixed
  let := metricSpace.{u, u} R hp hfixed
  exact Isometry.of_dist_eq (sourceCarrierMap_distance (R := R))

/-- Every original Cauchy sequence converges in the same original quotient
with its original independently sized target universe. -/
theorem cauchySeq_tendsto (s : ℕ → Space.{u, v} R)
    (hs : letI := metricSpace.{u, v} R hp hfixed; CauchySeq s) :
    letI := distanceTopology.{u, v} R
    ∃ a : Space.{u, v} R, Tendsto s atTop (𝓝 a) := by
  let := metricSpace.{u, v} R hp hfixed
  let := metricSpace.{u, u} R hp hfixed
  have hf := sourceCarrierMap_isometry.{u, v} R hp hfixed
  have hC : CauchySeq (sourceCarrierMap R ∘ s) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hs ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [Function.comp_apply, hf.dist_eq] using hN m hm n hn
  let : CompleteSpace (Space.{u, u} R) := commonCarrier_completeSpace R hp hfixed
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hC
  obtain ⟨m₀, -⟩ := Quotient.exists_rep (s 0)
  obtain ⟨b, hb⟩ := sourceCarrierMap_surjective_of_marked m₀ a
  refine ⟨b, hf.tendsto_nhds_iff.mpr ?_⟩
  rwa [hb]

/-- The original full-log Teichmüller metric of the original
general reference is complete in the book's given fixed-triple coordinates.
Targets may be open and have independent universes and native atlases. -/
theorem completeSpace :
    letI := metricSpace.{u, v} R hp hfixed
    CompleteSpace (Space.{u, v} R) := by
  let := metricSpace.{u, v} R hp hfixed
  exact Metric.complete_of_cauchySeq_tendsto (cauchySeq_tendsto R hp hfixed)

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
