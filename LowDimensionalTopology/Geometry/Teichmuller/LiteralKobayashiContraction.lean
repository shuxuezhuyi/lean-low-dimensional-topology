module

public import LowDimensionalTopology.Geometry.Teichmuller.LiteralKobayashiExtendedCore

/-!
# Holomorphic contraction of the disk-chain infima

Composition sends actual holomorphic disks and finite chains to the
corresponding disks and chains in the target. The costs remain extended
nonnegative real numbers, including for empty families. Two holomorphic
inverse maps preserve the resulting infimum.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff BigOperators

namespace LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore

open Surfaces

universe u v

variable {d e : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [ChartedSpace (Fin d → ℂ) M]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]
  [TopologicalSpace N] [ChartedSpace (Fin e → ℂ) N]
  [IsManifold 𝓘(ℂ, Fin e → ℂ) ω N]

/-- A holomorphic map contracts the one-disk infimum by composition of disks. -/
theorem oneDiskEDist_map_le {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω f) (p q : M) :
    oneDiskEDist (d := e) (f p) (f q) ≤ oneDiskEDist (d := d) p q := by
  let := discRiemannSurface.toRiemannAtlas.toChartedSpace
  conv_rhs => unfold oneDiskEDist
  refine le_iInf fun g => le_iInf fun hg => le_iInf fun a =>
    le_iInf fun b => le_iInf fun hga => le_iInf fun hgb => ?_
  simpa only [Function.comp_apply, hga, hgb] using!
    oneDiskEDist_le (d := e) (f := f ∘ g) (hf.comp hg) a b

/-- Applying a holomorphic map to every vertex contracts each finite-chain infimum. -/
theorem finiteChainEDist_map_le {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω f)
    (n : ℕ) (p q : M) :
    finiteChainEDist (d := e) n (f p) (f q) ≤ finiteChainEDist (d := d) n p q := by
  unfold finiteChainEDist
  refine le_iInf fun s => le_iInf fun h0 => le_iInf fun hq => ?_
  exact (finiteChainEDist_le_sum (d := e) n (f p) (f q) (f ∘ s)
    (congrArg f h0) (congrArg f hq)).trans
      (Finset.sum_le_sum fun i _ =>
        oneDiskEDist_map_le hf (s i.castSucc) (s i.succ))

/-- Holomorphic maps contract the extended Kobayashi infimum. -/
theorem kobayashiEDist_map_le {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω f) (p q : M) :
    kobayashiEDist (d := e) (f p) (f q) ≤ kobayashiEDist (d := d) p q := by
  unfold kobayashiEDist
  refine le_iInf fun n => ?_
  exact (iInf_le (fun m => finiteChainEDist (d := e) m (f p) (f q)) n).trans
    (finiteChainEDist_map_le hf n p q)

/-- A bijection whose two inverse maps are holomorphic preserves the extended infimum. -/
theorem kobayashiEDist_equiv (f : M ≃ N)
    (hf : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) ω (f : M → N))
    (hg : ContMDiff 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, Fin d → ℂ) ω (f.symm : N → M))
    (p q : M) :
    kobayashiEDist (d := e) (f p) (f q) = kobayashiEDist (d := d) p q := by
  apply le_antisymm
  · exact kobayashiEDist_map_le hf p q
  · simpa only [Equiv.symm_apply_apply] using kobayashiEDist_map_le hg (f p) (f q)

end LowDimensionalTopology.Geometry.Teichmuller.KobayashiCore
