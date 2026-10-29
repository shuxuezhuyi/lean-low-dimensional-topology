module

public import LowDimensionalTopology.Geometry.Teichmuller.IrreducibleNativeMinimizer
public import LowDimensionalTopology.Geometry.Teichmuller.ConditionalEllipticFiniteOrder
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalReducibleModularDichotomy
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalPseudoAnosovModularCharacterization

/-!
# The exclusive nonperiodic classification on the original surface

Finite cyclic conformal realization supplies an actual periodic representative
by conjugation with its own smooth positive marking. The original modular
dichotomies and the explicit pseudo-Anosov dynamic input then give the
exclusive alternatives for every original positive homeomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "AutR" =>
  @SourceQCModular.Aut X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- Ellipticity supplies an actual positive periodic representative through
the conformal realization of the same finite cyclic modular subgroup. -/
theorem exists_positive_periodic_of_isElliptic_of_nielsen
    (hNielsen : FiniteCyclicNielsenRealization R)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (q : AutR)
    (helliptic : let := R.toRiemannAtlas.toChartedSpace
      let := R.toRiemannAtlas.isManifold
      IsElliptic R (SourceQCModular.mk q)) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∃ h : X ≃ₜ X, IsOrientationPreservingRS h ∧ IsOfFinOrder h ∧
      ContinuousMap.Homotopic (SourceQCModular.continuousMap q)
        (_root_.toContinuousMap h) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.compactSpace
  let C := Subgroup.zpowers (SourceQCModular.mk q)
  have hfinite : Finite C := finite_zpowers.mpr
    (isOfFinOrder_of_isElliptic R hg hgenus (SourceQCModular.mk q) helliptic)
  obtain ⟨M, ρ, _hinjective, hmark⟩ :=
    hNielsen g hg hgenus C hfinite (inferInstance : IsCyclic C)
  let := M.surface.toRiemannAtlas.toChartedSpace
  let := M.surface.toRiemannAtlas.isManifold
  let F : X ≃ₜ M.carrier := M.marking.toHomeomorph
  let c : C := ⟨SourceQCModular.mk q, Subgroup.mem_zpowers (SourceQCModular.mk q)⟩
  let back : M.surface.toRiemannAtlas.analyticAutomorphismSubgroup →* (X ≃ₜ X) :=
    { toFun := fun u => (F.trans u.val).trans F.symm
      map_one' := by
        ext x
        exact F.symm_apply_apply x
      map_mul' := by
        intro u v
        ext x
        change F.symm (u.val (v.val (F x))) =
          F.symm (u.val (F (F.symm (v.val (F x)))))
        rw [F.apply_symm_apply] }
  have hF : IsQCRS F := M.marking.isQCRS_of_compact M.orientation_preserving
  have hrho : IsBiholomorphic ((ρ c).val : M.carrier → M.carrier) :=
    (analyticHomeomorph_iff_sourceBiholomorphic
      M.surface.toRiemannAtlas M.surface.toRiemannAtlas (ρ c).val).mp (ρ c).property
  have hrhoQC : IsQCRS (ρ c).val :=
    ⟨1, (isKQCRS_one_iff (ρ c).val).mpr hrho⟩
  have hpositive : IsOrientationPreservingRS (back (ρ c)) :=
    s28q_isOrientationPreservingRS_of_isQCRS
      (s28q_isQCRS_trans (s28q_isQCRS_trans hF hrhoQC) (s28q_isQCRS_symm hF))
  have hperiodic : IsOfFinOrder (back (ρ c)) := by
    let : Finite C := hfinite
    exact back.isOfFinOrder (ρ.isOfFinOrder (isOfFinOrder_of_finite c))
  have H := (ContinuousMap.Homotopic.refl (_root_.toContinuousMap F.symm)).comp
    (hmark c q rfl)
  have hleft : (_root_.toContinuousMap F.symm).comp
      ((_root_.toContinuousMap (ρ c).val).comp M.markingMap) =
        _root_.toContinuousMap (back (ρ c)) := by
    ext x
    rfl
  have hright : (_root_.toContinuousMap F.symm).comp
      (M.markingMap.comp (SourceQCModular.continuousMap q)) =
        SourceQCModular.continuousMap q := by
    ext x
    exact F.symm_apply_apply (q.val x)
  rw [hleft, hright] at H
  exact ⟨back (ρ c), hpositive, hperiodic, H.symm⟩

/-- An original positive map with no positive periodic homotopy representative
is homotopic to a pseudo-Anosov map or is reducible, and never both. -/
theorem original_nonperiodic_pseudoAnosov_or_reducible_exclusive
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hSimple : ∀ σ : PositiveComplexStructure R,
      LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives
        σ.surface g (σ.marked.geodesicLengthModel R (Nat.succ_le_of_lt hg) hgenus))
    (hCard : ∀ σ : PositiveComplexStructure R,
      LowDimensionalTopology.Unproved.Surfaces.ClosedDecomposingSystemCardinalities
        σ.surface (Nat.succ_le_of_lt hg) hgenus
        (σ.marked.geodesicLengthModel R (Nat.succ_le_of_lt hg) hgenus))
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    (hStraight : LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening
      R g)
    (hMumford : NativeMumfordSequentialCompactness R hg hgenus)
    (hNielsen : FiniteCyclicNielsenRealization R)
    (hReducible : OriginalReducibleModularDichotomy R g)
    (hPA : OriginalPseudoAnosovModularCharacterization R g)
    (f : X ≃ₜ X)
    (hf : let := R.toRiemannAtlas.toChartedSpace
      let := R.toRiemannAtlas.isManifold
      IsOrientationPreservingRS f)
    (hperiodic : ¬ ∃ h : X ≃ₜ X,
      (let := R.toRiemannAtlas.toChartedSpace; IsOrientationPreservingRS h) ∧
        IsOfFinOrder h ∧
          ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) :
    ((∃ h : X ≃ₜ X, IsPseudoAnosov R h ∧
        ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) ∨
      IsReducible f) ∧
      ¬ ((∃ h : X ≃ₜ X, IsPseudoAnosov R h ∧
        ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) ∧
          IsReducible f) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨q, hfq⟩ := exists_qc_representative R hg hgenus f hf
  have hPAiff := hPA hg hgenus f hf q hfq
  have hdisjoint : ¬ ((∃ h : X ≃ₜ X, IsPseudoAnosov R h ∧
      ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap h)) ∧
        IsReducible f) := by
    rintro ⟨hpa, hred⟩
    have hattained := (hPAiff.mp hpa).2
    rcases hReducible hg hgenus f hf hred hperiodic q hfq with hp | hph
    · exact hp.2 hattained
    · exact hph.2 hattained
  refine ⟨?_, hdisjoint⟩
  by_cases hred : IsReducible f
  · exact Or.inr hred
  · have hirred : IsIrreducible f := hred
    rcases elliptic_or_hyperbolic_of_irreducible_originalHomeomorph_of_mumford
        R hg hgenus hSimple hCard hCircle hStraight hMumford f hf hirred q hfq with he | hh
    · obtain ⟨h, hpositive, hfinite, hqh⟩ :=
        exists_positive_periodic_of_isElliptic_of_nielsen R hNielsen hg hgenus q he
      exact (hperiodic ⟨h, hpositive, hfinite, hfq.trans hqh⟩).elim
    · exact Or.inl (hPAiff.mpr hh)

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
