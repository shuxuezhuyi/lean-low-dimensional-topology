module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceQCModularAction
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarkingSurjectivity
public import LowDimensionalTopology.Geometry.Teichmuller.SourceUniverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# The two Bers extremal problems on the same original compact surface

Positive complex structures preserve the given real smooth structure and
orientation. Their marking is the literal identity. All actual marked
classes are supplied by pullback along a proved positive smooth marking.
Maximal dilatation is infinity for non-QC homeomorphisms. The original
complex-structure problem is compared with the full-log modular displacement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers

open Surfaces LiZhongQC
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- A complex structure on the unchanged smooth oriented reference surface. -/
structure PositiveComplexStructure where
  surface : ClosedRiemannSurface X
  identity : SmoothSurfaceEquiv R.toRiemannSurface surface.toRiemannSurface
  identity_map : identity.toHomeomorph = Homeomorph.refl X
  orientation_preserving :
    PreservesComplexOrientation R.toRiemannAtlas surface.toRiemannAtlas identity.toHomeomorph

namespace PositiveComplexStructure

variable {R}

/-- The actual identity-marked complex structure. -/
def marked (σ : PositiveComplexStructure R) : MarkedRiemannSurface.{u, u} R where
  carrier := X
  topology := inferInstance
  surface := σ.surface
  marking := σ.identity
  orientation_preserving := σ.orientation_preserving

/-- The original full QC-marked quotient point. -/
def point (σ : PositiveComplexStructure R) :
    letI := R.toRiemannAtlas.toChartedSpace
    TeichSpace X :=
  Quot.mk _ σ.marked.toSource

/-- The genuine QC predicate in the chosen original complex structure. -/
def IsQC (σ : PositiveComplexStructure R) (f : X ≃ₜ X) : Prop :=
  letI := σ.surface.toRiemannAtlas.toChartedSpace
  LiZhongQC.IsQCRS f

/-- The actual maximal dilatation computed in the chosen original atlas. -/
def nativeDilatation (σ : PositiveComplexStructure R) (f : X ≃ₜ X) : ℝ≥0∞ :=
  letI := σ.surface.toRiemannAtlas.toChartedSpace
  LiZhongQC.maxDilatationRS f

/-- The source convention assigns infinity to every non-QC self-homeomorphism. -/
def dilatation (σ : PositiveComplexStructure R) (f : X ≃ₜ X) : ℝ≥0∞ := by
  classical
  exact if σ.IsQC f then σ.nativeDilatation f else ⊤

theorem nativeDilatation_ne_top (σ : PositiveComplexStructure R) (f : X ≃ₜ X)
    (hf : σ.IsQC f) : σ.nativeDilatation f ≠ ⊤ := by
  let := σ.surface.toRiemannAtlas.toChartedSpace
  exact s29_m_maxDilatationRS_ne_top hf

theorem one_le_nativeDilatation_toReal (σ : PositiveComplexStructure R) (f : X ≃ₜ X)
    (hf : σ.IsQC f) : 1 ≤ (σ.nativeDilatation f).toReal := by
  let := σ.surface.toRiemannAtlas.toChartedSpace
  let := σ.surface.nonempty
  exact s29_m_one_le_toReal hf

/-- Comparing actual finite QC dilatations is equivalent to comparing their full logarithms. -/
theorem dilatation_le_iff_log (σ τ : PositiveComplexStructure R) (f g : X ≃ₜ X)
    (hf : σ.IsQC f) (hg : τ.IsQC g) :
    σ.dilatation f ≤ τ.dilatation g ↔
      Real.log (σ.nativeDilatation f).toReal ≤ Real.log (τ.nativeDilatation g).toReal := by
  simp only [dilatation, hf, hg, ↓reduceIte]
  have hf0 : 0 < (σ.nativeDilatation f).toReal :=
    lt_of_lt_of_le zero_lt_one (σ.one_le_nativeDilatation_toReal f hf)
  have hg0 : 0 < (τ.nativeDilatation g).toReal :=
    lt_of_lt_of_le zero_lt_one (τ.one_le_nativeDilatation_toReal g hg)
  constructor
  · intro h
    exact Real.log_le_log hf0
      (ENNReal.toReal_mono (τ.nativeDilatation_ne_top g hg) h)
  · intro h
    have h' := (Real.log_le_log_iff hf0 hg0).mp h
    rw [← ENNReal.ofReal_toReal (σ.nativeDilatation_ne_top f hf),
      ← ENNReal.ofReal_toReal (τ.nativeDilatation_ne_top g hg)]
    exact ENNReal.ofReal_le_ofReal h'

/-- Pull the actual target atlas back by its actual positive smooth marking. -/
def ofMarked (M : MarkedRiemannSurface.{u, u} R) : PositiveComplexStructure R := by
  let S := M.surface.pullbackHomeomorph M.marking.toHomeomorph
  let hS := M.surface.pullbackHomeomorph_analytic M.marking.toHomeomorph
  let e := SmoothSurfaceEquiv.ofConformalHomeomorph S.toRiemannSurface
    M.surface.toRiemannSurface M.marking.toHomeomorph hS
  refine
    { surface := S
      identity := SmoothSurfaceEquiv.trans M.marking (SmoothSurfaceEquiv.symm e)
      identity_map := ?_
      orientation_preserving := ?_ }
  · ext x
    change M.marking.toHomeomorph.symm (M.marking.toHomeomorph x) = x
    exact M.marking.toHomeomorph.symm_apply_apply x
  · have he := analyticHomeomorph_preservesComplexOrientation M.marking.toHomeomorph hS
    exact (PreservesComplexOrientation.homeomorph_symm M.marking.toHomeomorph he).comp
      M.orientation_preserving M.marking.toHomeomorph.continuous

/-- This is the same original marked class, with a genuine conformal target change. -/
theorem marked_ofMarked_equivalent (M : MarkedRiemannSurface.{u, u} R) :
    MarkedRiemannSurface.Equivalent (ofMarked M).marked M := by
  refine ⟨M.marking.toHomeomorph,
    M.surface.pullbackHomeomorph_analytic M.marking.toHomeomorph, ?_⟩
  have heq : (_root_.toContinuousMap M.marking.toHomeomorph).comp
      (ofMarked M).marked.markingMap = M.markingMap := by
    ext x
    change M.marking.toHomeomorph
      (M.marking.toHomeomorph.symm (M.marking.toHomeomorph x)) = M.marking.toHomeomorph x
    rw [M.marking.toHomeomorph.symm_apply_apply]
  change ContinuousMap.Homotopic
    ((_root_.toContinuousMap M.marking.toHomeomorph).comp
      (ofMarked M).marked.markingMap) M.markingMap
  rw [heq]

/-- All original QC-marked points have a literal identity-marked positive complex structure. -/
theorem point_surjective {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    Function.Surjective (point (R := R)) := by
  let := R.toRiemannAtlas.toChartedSpace
  intro p
  obtain ⟨a, ha⟩ := TeichmullerSpace.toSource_surjective R hg hgenus
    (canonicalHandleGroupPresentation g) p
  have hrep : ∃ σ : PositiveComplexStructure R, σ.point = TeichmullerSpace.toSource R a := by
    refine Quotient.inductionOn a ?_
    intro M
    refine ⟨ofMarked M, ?_⟩
    exact Quot.sound ((MarkedRiemannSurface.toSource_equiv_iff
      (ofMarked M).marked M).mpr (marked_ofMarked_equivalent M))
  obtain ⟨σ, hσ⟩ := hrep
  exact ⟨σ, hσ.trans ha⟩

end PositiveComplexStructure

/-- An actual jointly extremal pair, over all original structures and the entire homotopy class. -/
def IsAbsolutelyExtremal (f : X ≃ₜ X) (σ : PositiveComplexStructure R) (h : X ≃ₜ X) : Prop :=
  σ.IsQC h ∧ ContinuousMap.Homotopic (_root_.toContinuousMap h) (_root_.toContinuousMap f) ∧
    ∀ (τ : PositiveComplexStructure R) (k : X ≃ₜ X),
      ContinuousMap.Homotopic (_root_.toContinuousMap k) (_root_.toContinuousMap f) →
        σ.dilatation h ≤ τ.dilatation k

/-- The source's f-minimal complex structure; no displacement conclusion is a field. -/
def IsMinimalComplexStructure (f : X ≃ₜ X) (σ : PositiveComplexStructure R) : Prop :=
  ∃ h : X ≃ₜ X, IsAbsolutelyExtremal R f σ h

/-- The entire original extremal problem depends only on the actual free homotopy class. -/
theorem minimalComplexStructure_congr {f k : X ≃ₜ X}
    (hfk : ContinuousMap.Homotopic (_root_.toContinuousMap f) (_root_.toContinuousMap k))
    (σ : PositiveComplexStructure R) :
    IsMinimalComplexStructure R f σ ↔ IsMinimalComplexStructure R k σ := by
  constructor
  · rintro ⟨h, hh, hhf, hmin⟩
    exact ⟨h, hh, hhf.trans hfk,
      fun τ e hek => hmin τ e (hek.trans hfk.symm)⟩
  · rintro ⟨h, hh, hhk, hmin⟩
    exact ⟨h, hh, hhk.trans hfk.symm,
      fun τ e hef => hmin τ e (hef.trans hfk)⟩

local notation "QCPointR" =>
  @TeichSpace X _ R.toRiemannAtlas.toChartedSpace
local notation "AutR" =>
  @SourceQCModular.Aut X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold
local notation "ModularR" =>
  @SourceQCModular.ModularGroup X _ R.toRiemannAtlas.toChartedSpace R.toRiemannAtlas.isManifold

/-- The actual full-log displacement of the actual full QC modular action. -/
def displacement (γ : ModularR) (p : QCPointR) : ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  exact QCBookMetric.bookDistance p (γ • p)

def infimalDisplacement (γ : ModularR) : ℝ :=
  sInf (Set.range (displacement R γ))

def IsMinimizingPoint (γ : ModularR) (p : QCPointR) : Prop :=
  infimalDisplacement R γ = displacement R γ p

theorem bookDistance_comm (p q : QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    QCBookMetric.bookDistance p q = QCBookMetric.bookDistance q p := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  rw [QCBookMetric.bookDistance_eq_two_mul, QCBookMetric.bookDistance_eq_two_mul,
    s29_m_teichDistance_symm]

theorem displacement_inv (γ : ModularR) (p : QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    displacement R γ⁻¹ p = displacement R γ p := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have h := SourceQCModular.bookDistance_smul γ p (γ⁻¹ • p)
  rw [smul_inv_smul, bookDistance_comm] at h
  exact h.symm

theorem isMinimizingPoint_iff (γ : ModularR) (p : QCPointR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    IsMinimizingPoint R γ p ↔ ∀ q, displacement R γ p ≤ displacement R γ q := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have hb : BddBelow (Set.range (displacement R γ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    rw [displacement, QCBookMetric.bookDistance_eq_two_mul]
    exact mul_nonneg (by norm_num) (s29_m_teichDistance_nonneg _ _)
  constructor
  · intro hp q
    exact hp ▸ csInf_le hb ⟨q, rfl⟩
  · intro hp
    exact le_antisymm (csInf_le hb ⟨p, rfl⟩)
      (le_csInf ⟨_, ⟨p, rfl⟩⟩ (by rintro _ ⟨q, rfl⟩; exact hp q))

/-- Every admissible self-map bounds the true modular displacement, in the full-log normalization. -/
theorem displacement_le_log {f : AutR} (σ : PositiveComplexStructure R)
    {h : X ≃ₜ X} (hh : σ.IsQC h)
    (hhom : ContinuousMap.Homotopic (_root_.toContinuousMap h) (_root_.toContinuousMap f.val)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    displacement R (SourceQCModular.mk f) σ.point ≤
      Real.log (σ.nativeDilatation h).toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let m := σ.marked.toSource
  let n := SourceReferenceChange.marked f.val.symm (s28q_isQCRS_symm f.property) m
  have hm : m.marking = Homeomorph.refl X := σ.identity_map
  have hn : n.marking = f.val := by
    ext x
    change m.marking (f.val x) = f.val x
    rw [hm]
    rfl
  have hmark : ContinuousMap.Homotopic
      (_root_.toContinuousMap (m.marking.trans h))
      (_root_.toContinuousMap n.marking) := by
    rw [hm, hn]
    exact hhom
  have hclass : (Quot.mk _ n : QCPointR) =
      (SourceQCModular.mk f)⁻¹ • σ.point := rfl
  have hmem : Real.log (σ.nativeDilatation h).toReal ∈
      QCBookMetric.admissibleLogDilatations σ.point
        ((SourceQCModular.mk f)⁻¹ • σ.point) :=
    ⟨m, n, h, rfl, hclass, hh, hmark, rfl⟩
  have hb := csInf_le (QCBookMetric.admissibleLogDilatations_bddBelow _ _) hmem
  exact (displacement_inv R (SourceQCModular.mk f) σ.point) ▸ hb

/-- True distance attainment supplies an actual original homotopy-class self-map. -/
theorem displacement_attained {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (f : AutR) (σ : PositiveComplexStructure R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∃ h : X ≃ₜ X, σ.IsQC h ∧
      ContinuousMap.Homotopic (_root_.toContinuousMap h) (_root_.toContinuousMap f.val) ∧
      displacement R (SourceQCModular.mk f) σ.point =
        Real.log (σ.nativeDilatation h).toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let m := σ.marked.toSource
  let n := SourceReferenceChange.marked f.val.symm (s28q_isQCRS_symm f.property) m
  obtain ⟨h, hext, _, hmark, hd⟩ :=
    teichDistance_attained hg (R.hasSourceGenus hgenus) m n
  change X ≃ₜ X at h
  have hm : m.marking = Homeomorph.refl X := σ.identity_map
  have hn : n.marking = f.val := by
    ext x
    change m.marking (f.val x) = f.val x
    rw [hm]
    rfl
  have hhom : ContinuousMap.Homotopic (_root_.toContinuousMap h)
      (_root_.toContinuousMap f.val) := by
    change ContinuousMap.Homotopic
      (_root_.toContinuousMap ((m.marking : X ≃ₜ X).trans h))
      (_root_.toContinuousMap (n.marking : X ≃ₜ X)) at hmark
    rw [hm, hn] at hmark
    exact hmark
  have hclass : (Quot.mk _ n : QCPointR) =
      (SourceQCModular.mk f)⁻¹ • σ.point := rfl
  have hfull : displacement R (SourceQCModular.mk f)⁻¹ σ.point =
      Real.log (σ.nativeDilatation h).toReal := by
    change QCBookMetric.bookDistance (Quot.mk _ m : QCPointR)
      ((SourceQCModular.mk f)⁻¹ • σ.point) = _
    calc
      QCBookMetric.bookDistance (Quot.mk _ m : QCPointR)
          ((SourceQCModular.mk f)⁻¹ • σ.point) =
          QCBookMetric.bookDistance (Quot.mk _ m : QCPointR) (Quot.mk _ n : QCPointR) :=
        congrArg (QCBookMetric.bookDistance (Quot.mk _ m : QCPointR)) hclass.symm
      _ = 2 * teichDistance (Quot.mk _ m : QCPointR) (Quot.mk _ n : QCPointR) :=
        QCBookMetric.bookDistance_eq_two_mul _ _
      _ = 2 * ((1 / 2 : ℝ) * Real.log (σ.nativeDilatation h).toReal) := by
        exact congrArg (fun d : ℝ => 2 * d) hd
      _ = Real.log (σ.nativeDilatation h).toReal := by ring
  exact ⟨h, hext.1, hhom, (displacement_inv R _ _).symm.trans hfull⟩

/-- A structure is jointly minimal exactly at a genuine modular minimum-displacement point. -/
theorem minimalComplexStructure_iff_minimizingPoint
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (f : AutR) (σ : PositiveComplexStructure R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    IsMinimalComplexStructure R f.val σ ↔
      IsMinimizingPoint R (SourceQCModular.mk f) σ.point := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  rw [isMinimizingPoint_iff]
  constructor
  · rintro ⟨h, hh, hhom, hmin⟩ p
    obtain ⟨τ, rfl⟩ := PositiveComplexStructure.point_surjective hg hgenus p
    obtain ⟨k, hk, hkhom, hkd⟩ := displacement_attained R hg hgenus f τ
    exact (displacement_le_log R σ hh hhom).trans
      (((σ.dilatation_le_iff_log τ h k hh hk).mp (hmin τ k hkhom)).trans hkd.symm.le)
  · intro hmin
    obtain ⟨h, hh, hhom, hhd⟩ := displacement_attained R hg hgenus f σ
    refine ⟨h, hh, hhom, ?_⟩
    intro τ k hkhom
    by_cases hk : τ.IsQC k
    · apply (σ.dilatation_le_iff_log τ h k hh hk).mpr
      exact hhd ▸ (hmin τ.point).trans (displacement_le_log R τ hk hkhom)
    · simp only [PositiveComplexStructure.dilatation, hk, ↓reduceIte, le_top]

def IsElliptic (γ : ModularR) : Prop :=
  infimalDisplacement R γ = 0 ∧ ∃ p, IsMinimizingPoint R γ p

def IsHyperbolic (γ : ModularR) : Prop :=
  0 < infimalDisplacement R γ ∧ ∃ p, IsMinimizingPoint R γ p

/-- A jointly minimizing complex structure exists exactly in the elliptic or hyperbolic case. -/
theorem exists_minimalComplexStructure_iff_elliptic_or_hyperbolic
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (f : AutR) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    (∃ σ : PositiveComplexStructure R, IsMinimalComplexStructure R f.val σ) ↔
      IsElliptic R (SourceQCModular.mk f) ∨ IsHyperbolic R (SourceQCModular.mk f) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have hnonneg : 0 ≤ infimalDisplacement R (SourceQCModular.mk f) := by
    apply Real.sInf_nonneg
    rintro _ ⟨p, rfl⟩
    rw [displacement, QCBookMetric.bookDistance_eq_two_mul]
    exact mul_nonneg (by norm_num) (s29_m_teichDistance_nonneg _ _)
  constructor
  · rintro ⟨σ, hσ⟩
    have hp := (minimalComplexStructure_iff_minimizingPoint R hg hgenus f σ).mp hσ
    by_cases ha : infimalDisplacement R (SourceQCModular.mk f) = 0
    · exact Or.inl ⟨ha, σ.point, hp⟩
    · exact Or.inr ⟨lt_of_le_of_ne hnonneg (Ne.symm ha), σ.point, hp⟩
  · intro h
    have hp : ∃ p, IsMinimizingPoint R (SourceQCModular.mk f) p :=
      h.elim And.right And.right
    obtain ⟨p, hp⟩ := hp
    obtain ⟨σ, rfl⟩ := PositiveComplexStructure.point_surjective hg hgenus p
    exact ⟨σ, (minimalComplexStructure_iff_minimizingPoint R hg hgenus f σ).mpr hp⟩

/-- Every original orientation-preserving homeomorphism has an actual QC modular representative.
This uses the already proved DE representative and its true homotopy, with no smoothing premise. -/
theorem exists_qc_representative {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (f : X ≃ₜ X) (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      IsOrientationPreservingRS f) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∃ a : AutR,
      ContinuousMap.Homotopic (_root_.toContinuousMap f) (SourceQCModular.continuousMap a) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨F, hF, hhom⟩ := exists_smooth_in_homotopy_class_ofManifold hg
    (R.hasSourceGenus hgenus) (R.hasSourceGenus hgenus) f hf
  exact ⟨⟨F.toHomeomorph, F.isQCRS_of_compact hF⟩, hhom⟩

/-- The complete extremal comparison for the supplied original homeomorphism.
The modular representative is supplied, and the comparison is for every original structure. -/
theorem originalHomeomorph_minimizer_comparison
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (f : X ≃ₜ X) (hf : letI := R.toRiemannAtlas.toChartedSpace
      letI := R.toRiemannAtlas.isManifold
      IsOrientationPreservingRS f) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∃ a : AutR,
      ContinuousMap.Homotopic (_root_.toContinuousMap f) (SourceQCModular.continuousMap a) ∧
      (∀ σ : PositiveComplexStructure R,
        IsMinimalComplexStructure R f σ ↔
          IsMinimizingPoint R (SourceQCModular.mk a) σ.point) ∧
      ((∃ σ : PositiveComplexStructure R, IsMinimalComplexStructure R f σ) ↔
        IsElliptic R (SourceQCModular.mk a) ∨ IsHyperbolic R (SourceQCModular.mk a)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨a, ha⟩ := exists_qc_representative R hg hgenus f hf
  refine ⟨a, ha, ?_, ?_⟩
  · intro σ
    exact (minimalComplexStructure_congr R ha σ).trans
      (minimalComplexStructure_iff_minimizingPoint R hg hgenus a σ)
  · have he : (∃ σ : PositiveComplexStructure R, IsMinimalComplexStructure R f σ) ↔
        ∃ σ : PositiveComplexStructure R, IsMinimalComplexStructure R a.val σ := by
      constructor
      · rintro ⟨σ, hσ⟩
        exact ⟨σ, (minimalComplexStructure_congr R ha σ).mp hσ⟩
      · rintro ⟨σ, hσ⟩
        exact ⟨σ, (minimalComplexStructure_congr R ha σ).mpr hσ⟩
    exact he.trans
      (exists_minimalComplexStructure_iff_elliptic_or_hyperbolic R hg hgenus a)

end LowDimensionalTopology.Geometry.Teichmuller.NativeMinimizers
