module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairFreeGroup
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.DiscretenessCriteria
public import Mathlib.GroupTheory.Finiteness

@[expose] public section
noncomputable section
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions

/-- Exactly the disc subgroup of the original annular pair group's Cayley data. -/
def annularPairReflectionDiscGroup (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    Subgroup Mobius.complexMobiusGroup :=
  subgroupConjugate cayleyMobius
    (Fuchsian.nativeConformalSubgroupMobiusHom
      (annularPairReflectionGroup E r x hE hr)
      (annularPairReflectionGroup_le_conformal E r x hE hr)).range

/-- The original free basis is preserved through the actual faithful image and Cayley chart. -/
def annularPairReflectionDiscFreeEquiv (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hin : 1 + r < x) (hout : x + r < E) :
    FreeGroup (Fin 2) ≃* annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr := by
  let K := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let hK := annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr
  let F := Fuchsian.nativeConformalSubgroupMobiusHom K hK
  exact (annularPairReflectionFreeEquiv E r x hE hr hin hout).trans
    ((MonoidHom.ofInjective
      (Fuchsian.nativeConformalSubgroupMobiusHom_isometry K hK).injective).trans
      (subgroupConjugateEquivalence cayleyMobius F.range))

theorem annularPairReflectionDiscFreeEquiv_coe (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hin : 1 + r < x) (hout : x + r < E)
    (w : FreeGroup (Fin 2)) :
    (annularPairReflectionDiscFreeEquiv E r x hE hr hin hout w : Mobius.complexMobiusGroup) =
      cayleyMobius *
        Fuchsian.nativeConformalSubgroupMobiusHom
          (annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr)
          (annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr)
          (annularPairReflectionFreeEquiv E r x hE hr hin hout w) * cayleyMobius⁻¹ := rfl

theorem annularPairReflectionDiscGroup_fg (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hin : 1 + r < x) (hout : x + r < E) :
    (annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr).FG := by
  let e := annularPairReflectionDiscFreeEquiv E r x hE hr hin hout
  exact (Group.fg_iff_subgroup_fg _).mp
    (Group.fg_of_surjective (f := e.toMonoidHom) e.surjective)

theorem annularPairReflectionDiscGroup_isMulTorsionFree (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hin : 1 + r < x) (hout : x + r < E) :
    IsMulTorsionFree (annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr) := by
  let e := annularPairReflectionDiscFreeEquiv E r x hE hr hin hout
  exact Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective

/-- No elliptic of the same actual disc group survives the transferred torsion-free property. -/
theorem annularPairReflectionDiscGroup_noElliptic (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hin : 1 + r < x) (hout : x + r < E) :
    ∀ f ∈ annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr,
      f ≠ 1 → ¬ Mobius.MobiusElliptic f := by
  let G := annularPairReflectionDiscGroup E r x (zero_lt_one.trans hE) hr
  let P := (annularPairReflectionHalfPlaneData E r x hE hr hin hout).cayleyData
  let : IsMulTorsionFree G :=
    annularPairReflectionDiscGroup_isMulTorsionFree E r x hE hr hin hout
  intro f hf hne hell
  have hfin := DiscreteGroups.discrete_elliptic_finiteOrder G P.asFuchsianDisc.discrete f hf hell
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  have hfinG : IsOfFinOrder (⟨f, hf⟩ : G) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext hpow⟩
  exact hne (congrArg Subtype.val hfinG.eq_one')

end LowDimensionalTopology.Geometry.Hyperbolic
