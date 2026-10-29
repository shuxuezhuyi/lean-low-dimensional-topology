/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaSourceRealization

public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

/-- The actual native class of any source coefficient gives the same source
Teichmüller point, because normalized solutions depend only on the a.e. class. -/
theorem sourcePoint_fromSourceGamma {Γ : Subgroup Deck}
    (μ : LiZhongQC.BeltramiGamma Γ) :
    (Quotient.mk _ (toSourceGamma (fromSourceGamma μ)) : LiZhongQC.TeichGamma Γ) =
      Quotient.mk _ μ := by
  refine Quotient.sound (s := LiZhongQC.teichSetoidGamma Γ) ?_
  intro x
  obtain ⟨k, hk0, hk1, hμ⟩ :=
    LiZhongQC.bg_beltramiH_upper (toSourceGamma (fromSourceGamma μ)).val
  obtain ⟨l, hl0, hl1, hν⟩ := LiZhongQC.bg_beltramiH_upper μ.val
  have he := LiZhongQC.s27u_fSym_congr_ae hk0 hk1 hμ hl0 hl1 hν
    (toSourceGamma_fromSourceGamma_ae μ)
  simpa only [LiZhongQC.s33v_fSym_eq] using congrFun he (x : ℂ)

/-- The chosen representative of every actual source point has a native
compatible coefficient class representing precisely that point. -/
theorem sourcePoint_fromSourceGamma_out {Γ : Subgroup Deck}
    (q : LiZhongQC.TeichGamma Γ) :
    (Quotient.mk _ (toSourceGamma (fromSourceGamma q.out)) : LiZhongQC.TeichGamma Γ) =
      q :=
  (sourcePoint_fromSourceGamma q.out).trans (Quotient.out_eq q)

/-- Every source point is represented by an actual element of the existing
native compatible L-infinity ball, without any projection-surjectivity premise. -/
theorem exists_nativeBall_sourcePoint {Γ : Subgroup Deck}
    (q : LiZhongQC.TeichGamma Γ) :
    ∃ μ : Ball Γ, (Quotient.mk _ (toSourceGamma μ) : LiZhongQC.TeichGamma Γ) = q :=
  ⟨fromSourceGamma q.out, sourcePoint_fromSourceGamma_out q⟩

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
