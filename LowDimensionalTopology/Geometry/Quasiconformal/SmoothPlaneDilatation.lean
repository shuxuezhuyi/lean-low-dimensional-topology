module

public import LowDimensionalTopology.External.LiZhongQC.Ch01.S06_C1Quasiconformal
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The finite domain bound in the source's smooth quasiconformal definition

Use the existing plane predicate and literal maximal-dilatation supremum.
The smoothness hypothesis is explicit, and no compactness is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- On an actual smooth positive domain homeomorphism, the imported C¹
predicate says exactly that the literal quotient has one finite global bound. -/
theorem exists_isC1Quasiconformal_iff_bddAbove_of_smooth
    {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hC : ContDiffOn ℝ ∞ f D)
    (hhomeo : LiZhongQC.IsHomeomorphOnto f D (f '' D))
    (hJ : ∀ z ∈ D, 0 < LiZhongQC.jacobian f z) :
    (∃ K : ℝ, LiZhongQC.IsC1Quasiconformal f D K) ↔
      BddAbove (LiZhongQC.dilatationQuotient f '' D) := by
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hK.2.2.2.2 z hz).2
  · rintro ⟨K, hK⟩
    refine ⟨max 1 K, hD, le_max_left _ _, hC.of_le (by simp), hhomeo, ?_⟩
    intro z hz
    constructor
    · have h := hJ z hz
      unfold LiZhongQC.jacobian at h
      nlinarith [norm_nonneg (LiZhongQC.dzbar f z), norm_nonneg (LiZhongQC.dz f z)]
    · exact (hK (mem_image_of_mem _ hz)).trans (le_max_right _ _)

/-- On every nonempty QC domain, the existing real supremum is the genuine
least upper bound of the source's literal pointwise quotients. -/
theorem isLUB_maxDilatationC1_of_isC1Quasiconformal
    {f : ℂ → ℂ} {D : Set ℂ} {K : ℝ}
    (hf : LiZhongQC.IsC1Quasiconformal f D K) (hne : D.Nonempty) :
    IsLUB (LiZhongQC.dilatationQuotient f '' D) (LiZhongQC.maxDilatationC1 f D) := by
  change IsLUB (LiZhongQC.dilatationQuotient f '' D)
    (sSup (LiZhongQC.dilatationQuotient f '' D))
  have hbdd : BddAbove (LiZhongQC.dilatationQuotient f '' D) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hf.2.2.2.2 z hz).2
  exact isLUB_csSup (hne.image _) hbdd

end LowDimensionalTopology.Geometry.Quasiconformal
