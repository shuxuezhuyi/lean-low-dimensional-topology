/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ConformalTypes
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S24_QuasiFuchsian

/-!
# The same real matrix action on the entire compactified complex plane

Both actions have the identical fractional-linear coefficient formulas,
including a finite pole and infinity. No density argument is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The native and source real matrix actions agree on every sphere point,
including finite poles and infinity. -/
theorem realSLMobius_source_action (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ((Hyperbolic.realSLMobius A).val : OnePoint ℂ → OnePoint ℂ) =
      LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex A) := by
  funext z
  rw [Hyperbolic.realSLMobius, MonoidHom.comp_apply,
    Mobius.invariantDisc_specialLinear_action, LiZhongQC.k24_mobiusSL_real]
  induction z using OnePoint.rec with
  | infty =>
      rw [Mobius.fractionalLinear_infty]
      rfl
  | coe z =>
      rw [Mobius.fractionalLinear_coe]
      rfl

end LowDimensionalTopology.Geometry.Teichmuller
