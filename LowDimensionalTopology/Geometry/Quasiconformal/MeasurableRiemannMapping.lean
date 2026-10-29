module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S13_Representation
public import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Normalized measurable Riemann mappings

The solution is an actual homeomorphism of the plane, absolutely continuous on
lines and a generalized solution of the Beltrami equation. Its extension to the
Riemann sphere fixes infinity as well as zero and one.

The analytic existence and uniqueness proof is due to Wu Xiaobin; exact source,
license and local compatibility changes are recorded in the external module's
provenance manifest.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Topology
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Uniqueness holds among all normalized solutions, without prescribing an
extra distortion bound or extra regularity in the uniqueness hypothesis. -/
theorem normalized_beltrami_homeomorph_unique {μ : ℂ → ℂ} {f g : ℂ ≃ₜ ℂ}
    (hf : LiZhongQC.IsNormalizedSolution f μ)
    (hg : LiZhongQC.IsNormalizedSolution g μ) : f = g := by
  have hfg : (f : ℂ → ℂ) = g := LiZhongQC.thm13_5_uniqueness_plane
    hf.1 hg.1 hf.2.1 hg.2.1 (Filter.EventuallyEq.trans hf.2.2.2.2 (Filter.EventuallyEq.symm hg.2.2.2.2))
    hf.2.2.1 hf.2.2.2.1 hg.2.2.1 hg.2.2.2.1
  exact Homeomorph.ext (fun z => congrFun hfg z)

/-- The normalized plane solution, returned as a genuine homeomorphism together
with its sharp distortion bound, ACL regularity and generalized Beltrami equation. -/
theorem normalized_beltrami_homeomorph_existsUnique
    {μ : ℂ → ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ univ k) :
    ∃! f : ℂ ≃ₜ ℂ,
      LiZhongQC.IsNormalizedSolution f μ ∧
      LiZhongQC.IsKQC f univ ((1 + k) / (1 - k)) ∧
      LiZhongQC.IsACL f univ ∧ LiZhongQC.IsGenHomeoSolution f μ univ 2 := by
  obtain ⟨f, hfn, hfK, hfu⟩ := LiZhongQC.thm13_7_normalized_existence hk₀ hk hμ
  obtain ⟨e, he⟩ := LiZhongQC.t1_homeomorph hfK hfn.2.1
  have hen : LiZhongQC.IsNormalizedSolution e μ := by simpa only [he] using hfn
  have heK : LiZhongQC.IsKQC e univ ((1 + k) / (1 - k)) := by
    simpa only [he] using hfK
  have heμ : ∀ᵐ z ∂(volume.restrict (univ : Set ℂ)),
      LiZhongQC.complexDilatation e z = μ z := by
    simpa only [Measure.restrict_univ] using hen.2.2.2.2
  have hes : LiZhongQC.IsGenHomeoSolution e μ univ 2 :=
    LiZhongQC.nxS_genHomeoSolution_congr
      (LiZhongQC.thm10_2_genHomeoSolution_of_isKQC heK).2 heμ
  refine ⟨e, ⟨hen, heK, LiZhongQC.thm9_1_isACL heK, hes⟩, ?_⟩
  intro g hg
  apply Homeomorph.ext
  intro z
  exact congrFun ((hfu g hg.1).trans he.symm) z

/-- Normalization at zero and one extends to three-point normalization on the sphere. -/
theorem normalized_solution_sphere_normalization {μ : ℂ → ℂ} (f : ℂ ≃ₜ ℂ)
    (hf : LiZhongQC.IsNormalizedSolution f μ) :
    f.onePointCongr (∞ : OnePoint ℂ) = ∞ ∧
      f.onePointCongr ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) ∧
      f.onePointCongr ((1 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ) := by
  refine ⟨rfl, ?_, ?_⟩
  · change ((f 0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
    rw [hf.2.2.1]
  · change ((f 1 : ℂ) : OnePoint ℂ) = ((1 : ℂ) : OnePoint ℂ)
    rw [hf.2.2.2.1]

/-- Almost-everywhere equal coefficients have exactly the same normalized solutions. -/
theorem isNormalizedSolution_congr_ae {μ ν f : ℂ → ℂ} (hμν : μ =ᵐ[volume] ν) :
    LiZhongQC.IsNormalizedSolution f μ ↔ LiZhongQC.IsNormalizedSolution f ν := by
  constructor
  · rintro ⟨hq, hs, h0, h1, hd⟩
    exact ⟨hq, hs, h0, h1, Filter.EventuallyEq.trans hd hμν⟩
  · rintro ⟨hq, hs, h0, h1, hd⟩
    exact ⟨hq, hs, h0, h1, Filter.EventuallyEq.trans hd hμν.symm⟩

end LowDimensionalTopology.Geometry.Quasiconformal
