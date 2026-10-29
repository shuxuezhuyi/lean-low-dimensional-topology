module

public import LowDimensionalTopology.Geometry.Teichmuller.EllipticFiniteOrder
public import LowDimensionalTopology.Unproved.Teichmuller.FiniteCyclicNielsenRealization
public import Mathlib.Data.ZMod.QuotientGroup

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "QCPointR" => @TeichSpace X _ R.toRiemannAtlas.toChartedSpace
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- Coherent conformal realization fixes one actual marked point for the entire cyclic subgroup. -/
theorem exists_common_fixedPoint_of_finite_cyclic_realization
    (hNielsen : FiniteCyclicNielsenRealization R)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (C : Subgroup ModularR) (hfinite : Finite C) (hcyclic : IsCyclic C) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∃ p : QCPointR, ∀ c : C, c.val • p = p := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨M, ρ, _hinjective, hmark⟩ := hNielsen g hg hgenus C hfinite hcyclic
  let m : MarkedRS X := M.toSource
  refine ⟨Quot.mk _ m, ?_⟩
  intro c
  obtain ⟨f, hf⟩ :=
    QuotientGroup.mk'_surjective (SourceQCModular.homotopyIdentitySubgroup X) c.val
  have hf' : SourceQCModular.mk f = c.val := hf
  rw [← hf', SourceQCModular.mk_smul_mk]
  apply Quot.sound
  refine ⟨(ρ c).val, ?_, ?_⟩
  · exact (analyticHomeomorph_iff_sourceBiholomorphic
      M.surface.toRiemannAtlas M.surface.toRiemannAtlas (ρ c).val).mp (ρ c).property
  · have hh := (hmark c f hf').comp
      (ContinuousMap.Homotopic.refl (_root_.toContinuousMap f.val.symm))
    have hcancel : (M.markingMap.comp (SourceQCModular.continuousMap f)).comp
        (_root_.toContinuousMap f.val.symm) = M.markingMap := by
      ext x
      exact congrArg M.marking.toHomeomorph (f.val.apply_symm_apply x)
    rw [hcancel] at hh
    exact hh

/-- On the full original modular group, the finite-order criterion follows from cyclic Nielsen realization. -/
theorem isElliptic_iff_isOfFinOrder_of_nielsen
    (hNielsen : FiniteCyclicNielsenRealization R)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (γ : ModularR) :
    IsElliptic R γ ↔ IsOfFinOrder γ := by
  constructor
  · exact isOfFinOrder_of_isElliptic R hg hgenus γ
  · intro hγ
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    let C := Subgroup.zpowers γ
    have hfinite : Finite C := finite_zpowers.mpr hγ
    obtain ⟨p, hp⟩ := exists_common_fixedPoint_of_finite_cyclic_realization
      R hNielsen hg hgenus C hfinite (inferInstance : IsCyclic (Subgroup.zpowers γ))
    have hfix : γ • p = p := hp ⟨γ, Subgroup.mem_zpowers γ⟩
    have hzero : displacement R γ p = 0 := by
      unfold displacement
      rw [hfix, QCBookMetric.bookDistance_eq_two_mul, s29_m_teichDistance_self, mul_zero]
    have hmin : IsMinimizingPoint R γ p := (isMinimizingPoint_iff R γ p).mpr (by
      intro q
      rw [hzero]
      unfold displacement
      rw [QCBookMetric.bookDistance_eq_two_mul]
      exact mul_nonneg (by norm_num) (s29_m_teichDistance_nonneg _ _))
    exact ⟨hmin.trans hzero, p, hmin⟩

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
