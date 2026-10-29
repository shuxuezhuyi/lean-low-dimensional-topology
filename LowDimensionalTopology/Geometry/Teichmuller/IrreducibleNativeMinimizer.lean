module

public import LowDimensionalTopology.Geometry.Surfaces.IrreducibleGeodesicLengthBound
public import LowDimensionalTopology.Geometry.Teichmuller.NativeMumfordMinimizer
public import Mathlib.Topology.Order.IsLUB

/-!
# Native minimum displacement for irreducible original maps

An actual decreasing displacement sequence has identity-marked positive
complex structures and actual extremal self-homeomorphisms. Their bounded
full logarithmic dilatations and the simple-geodesic length bound give a
single strict lower length bound on every original simple free class.
The explicit native Mumford input then supplies a true minimizing point.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local notation "AutR" =>
  @SourceQCModular.Aut X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- Actual positive structures and actual homotopy-class extremal maps realize
a decreasing sequence tending to the full original displacement infimum. -/
theorem exists_identity_marked_minimizing_sequence
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (a : AutR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∃ (σs : ℕ → PositiveComplexStructure R) (hs : ℕ → X ≃ₜ X),
      Antitone (fun n => displacement R (SourceQCModular.mk a) (σs n).point) ∧
        Tendsto (fun n => displacement R (SourceQCModular.mk a) (σs n).point)
          atTop (𝓝 (infimalDisplacement R (SourceQCModular.mk a))) ∧
        ∀ n, (σs n).IsQC (hs n) ∧
          ContinuousMap.Homotopic (_root_.toContinuousMap (hs n))
            (_root_.toContinuousMap a.val) ∧
          displacement R (SourceQCModular.mk a) (σs n).point =
            Real.log ((σs n).nativeDilatation (hs n)).toReal := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let S : Set ℝ := range (displacement R (SourceQCModular.mk a))
  have hS : S.Nonempty :=
    ⟨_, ⟨TeichmullerSpace.toSource R (TeichmullerSpace.basePoint R), rfl⟩⟩
  have hb : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    rw [displacement, QCBookMetric.bookDistance_eq_two_mul]
    exact mul_nonneg (by norm_num) (s29_m_teichDistance_nonneg _ _)
  obtain ⟨u, huanti, hulim, humem⟩ := exists_seq_tendsto_sInf hS hb
  have hrep (n : ℕ) : ∃ σ : PositiveComplexStructure R,
      displacement R (SourceQCModular.mk a) σ.point = u n := by
    obtain ⟨p, hp⟩ := humem n
    obtain ⟨σ, hσ⟩ := PositiveComplexStructure.point_surjective (R := R) hg hgenus p
    refine ⟨σ, ?_⟩
    rw [hσ]
    exact hp
  choose σs hσs using hrep
  choose hs hqc hhom hlog using fun n : ℕ => displacement_attained R hg hgenus a (σs n)
  have hfunctions : (fun n => displacement R (SourceQCModular.mk a) (σs n).point) = u :=
    funext hσs
  refine ⟨σs, hs, ?_, ?_, fun n => ⟨hqc n, hhom n, hlog n⟩⟩
  · simpa only [hfunctions] using huanti
  · simpa only [hfunctions, infimalDisplacement, S] using hulim

/-- Irreducibility forces a native minimum, with the two geometric classical
inputs explicitly supplied on every actual positive complex structure. -/
theorem exists_native_minimizingPoint_of_irreducible_of_mumford
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
    (hMumford : LowDimensionalTopology.Unproved.Teichmuller.NativeMumfordSequentialCompactness
      R hg hgenus)
    (a : AutR) (hirred : IsIrreducible a.val) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∃ p : TeichmullerSpace.{0, 0} R,
      IsMinimizingPoint R (SourceQCModular.mk a) (TeichmullerSpace.toSource R p) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.connectedSpace
  obtain ⟨σs, hs, hanti, hlim, hmaps⟩ :=
    exists_identity_marked_minimizing_sequence R hg hgenus a
  let γ : ModularR := SourceQCModular.mk a
  let K (n : ℕ) : ℝ := ((σs n).nativeDilatation (hs n)).toReal
  let d (n : ℕ) : ℝ := displacement R γ (σs n).point
  let A : ℝ := Real.exp (d 0) + 1
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hKpos (n : ℕ) : 0 < K n :=
    zero_lt_one.trans_le ((σs n).one_le_nativeDilatation_toReal (hs n) (hmaps n).1)
  have hKle (n : ℕ) : K n ≤ A := by
    have hlog : Real.log (K n) ≤ d 0 := by
      rw [← (show d n = Real.log (K n) from (hmaps n).2.2)]
      exact hanti (Nat.zero_le n)
    calc
      K n = Real.exp (Real.log (K n)) := (Real.exp_log (hKpos n)).symm
      _ ≤ Real.exp (d 0) := Real.exp_le_exp.mpr hlog
      _ ≤ A := by dsimp only [A]; linarith
  let δ : ℝ := shortClosedGeodesicCutoff / (2 * A ^ (3 * g - 3))
  have hApow : 0 < A ^ (3 * g - 3) := pow_pos hApos _
  have hδpos : 0 < δ :=
    div_pos shortClosedGeodesicCutoff_pos (mul_pos (by norm_num) hApow)
  have hStraightσ (σ : PositiveComplexStructure R) :
      LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening
        σ.surface g := by
    intro _hg _hgenus
    exact hStraight hg hgenus
  let points (n : ℕ) : TeichmullerSpace.{0, 0} R := TeichmullerSpace.mk (σs n).marked
  have hthickness (n : ℕ) (c : EssentialSimpleFreeClass X) :
      δ < (markedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus (points n) c : ℝ) := by
    refine Quotient.inductionOn c ?_
    intro c
    let := (σs n).surface.toRiemannAtlas.toChartedSpace
    let M := (σs n).marked.geodesicLengthModel R (Nat.succ_le_of_lt hg) hgenus
    obtain ⟨q, hq, hqi⟩ := hSimple (σs n) (Nat.succ_le_of_lt hg) hgenus c
    have hfK : IsKQCRS (hs n) (K n) := s29_m_isKQCRS_maxDil (hmaps n).1
    have hirredn : IsIrreducible (hs n) :=
      (isIrreducible_congr (hmaps n).2.1).mpr hirred
    have hpower := shortCutoff_le_pow_mul_length_of_irreducible
      (σs n).surface (Nat.succ_le_of_lt hg) hgenus M
      (hSimple (σs n)) (hCard (σs n)) hCircle (hStraightσ (σs n))
      (hs n) hfK hirredn q hqi
    have hbound : shortClosedGeodesicCutoff ≤ A ^ (3 * g - 3) * q.length.toReal :=
      hpower.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (hKpos n).le (hKle n) _) q.length_toReal_pos.le)
    have hmark : (σs n).marked.markingMap = ContinuousMap.id X := by
      ext x
      change (σs n).identity.toHomeomorph x = x
      exact congrArg (fun e : X ≃ₜ X => e x) (σs n).identity_map
    have hmarkLoop : FreelyHomotopic
        ⟨(σs n).marked.markingMap (circleRepresentativeLoop c.val).1,
          (circleRepresentativeLoop c.val).2.map (σs n).marked.markingMap.continuous⟩
        (circleRepresentativeLoop c.val) := by
      apply s30b_fh_of_eq
      intro t
      exact congrArg (fun e : C(X, X) => e ((circleRepresentativeLoop c.val).2 t)) hmark
    have hlength :
        (markedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus
          (TeichmullerSpace.mk (σs n).marked) c.freeClass : ℝ) = q.length.toReal :=
      markedLengthSpectrum_mk_eq R (Nat.succ_le_of_lt hg) hgenus c
        (σs n).marked M q (s30b_fh_trans hmarkLoop hq)
    change δ < (markedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus
      (TeichmullerSpace.mk (σs n).marked) c.freeClass : ℝ)
    rw [hlength]
    change shortClosedGeodesicCutoff / (2 * A ^ (3 * g - 3)) < q.length.toReal
    apply (div_lt_iff₀ (mul_pos (by norm_num) hApow)).2
    nlinarith [shortClosedGeodesicCutoff_pos]
  have hpoint (n : ℕ) : TeichmullerSpace.toSource R (points n) = (σs n).point := rfl
  have hlimNative :
      Tendsto (fun n => displacement R γ (TeichmullerSpace.toSource R (points n)))
        atTop (𝓝 (infimalDisplacement R γ)) := by
    simpa only [hpoint] using hlim
  exact exists_native_minimizingPoint_of_mumford_and_thick_minimizing_sequence
    R hg hgenus hMumford γ points ⟨δ, hδpos, hthickness⟩ hlimNative

/-- Every QC representative of an original positive irreducible homeomorphism
has an elliptic or hyperbolic original modular class under the explicit inputs. -/
theorem elliptic_or_hyperbolic_of_irreducible_originalHomeomorph_of_mumford
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
    (hMumford : LowDimensionalTopology.Unproved.Teichmuller.NativeMumfordSequentialCompactness
      R hg hgenus)
    (f : X ≃ₜ X)
    (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      IsOrientationPreservingRS f) (hirred : IsIrreducible f) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ q : SourceQCModular.Aut X,
      ContinuousMap.Homotopic (_root_.toContinuousMap f) (SourceQCModular.continuousMap q) →
        IsElliptic R (SourceQCModular.mk q) ∨ IsHyperbolic R (SourceQCModular.mk q) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨a, ha⟩ := exists_qc_representative R hg hgenus f hf
  have ha' : ContinuousMap.Homotopic (_root_.toContinuousMap f)
      (_root_.toContinuousMap a.val) := by
    simpa only [SourceQCModular.continuousMap] using ha
  have hirreda : IsIrreducible a.val := (isIrreducible_congr ha').mp hirred
  obtain ⟨p, hp⟩ := exists_native_minimizingPoint_of_irreducible_of_mumford
    R hg hgenus hSimple hCard hCircle hStraight hMumford a hirreda
  have hminimum : ∃ z, IsMinimizingPoint R (SourceQCModular.mk a) z :=
    ⟨TeichmullerSpace.toSource R p, hp⟩
  have htype : IsElliptic R (SourceQCModular.mk a) ∨ IsHyperbolic R (SourceQCModular.mk a) := by
    by_cases hz : infimalDisplacement R (SourceQCModular.mk a) = 0
    · exact Or.inl ⟨hz, hminimum⟩
    · exact Or.inr ⟨lt_of_le_of_ne (infimalDisplacement_nonneg R _) (Ne.symm hz), hminimum⟩
  exact fun q hq => by
    have heq : SourceQCModular.mk q = SourceQCModular.mk a :=
      (SourceQCModular.mk_eq_mk_iff_homotopic q a).2 (hq.symm.trans ha)
    simpa only [heq] using htype

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
