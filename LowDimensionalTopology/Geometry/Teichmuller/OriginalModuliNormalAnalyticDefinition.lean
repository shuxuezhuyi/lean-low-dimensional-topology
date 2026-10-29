module

public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersMetric
public import LowDimensionalTopology.Geometry.Teichmuller.CompactGenusModuliTopology
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# A concrete analytic presentation on the original fixed-genus quotient

The carrier, topology and projection are the actual original ones. Functions
are holomorphic precisely through their pullbacks on the actual Bers domain.
Point germs are formed from those functions. Local finite quotients must also
be realized by finitely many analytic equations, with the same local function
structure. No existence of such presentations or normality is proved here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
variable (hΓ : LiZhongQC.IsFuchsian Γ) {p : UpperHalfPlane → X}
variable (hp : letI := R.toRiemannAtlas.toChartedSpace;
  LiZhongQC.IsUniformization Γ p)

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "Q" => CompactGenusModuliSpace g
local notation "hfree" =>
  @LiZhongQC.s27g_actsFreely X inferInstance R.toRiemannAtlas.toChartedSpace Γ p hp
local notation "Bers" => TeichmullerSpace.bersCoordinates R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp

/-- The original projection, written on its actual Bers coordinate range. -/
def originalModuliBersProjection (z : Set.range Bers) : Q := by
  letI : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.fromQCMetricSpace R hg hgenus (canonicalHandleGroupPresentation g)
  exact TeichmullerSpace.toCompactGenusModuli R hgenus
    ((TeichmullerSpace.fromQCBersCoordinateHomeomorph R hg hgenus
      (canonicalHandleGroupPresentation g) hΓ hfree hp).symm z)

/-- Extend the projection only to write ambient pullback functions. No
continuity or analyticity outside the actual Bers range is asserted. -/
def originalModuliAmbientProjection (z : E) : Q := by
  classical
  exact if hz : z ∈ Set.range Bers then
    originalModuliBersProjection R hg hgenus hΓ hp ⟨z, hz⟩
  else
    TeichmullerSpace.toCompactGenusModuli R hgenus
      (TeichmullerSpace.mk (MarkedRiemannSurface.refl R))

/-- Actual local holomorphic functions, tested only above the specified open
set and inside the actual Bers domain. Zero extension is only a presentation. -/
def IsOriginalModuliHolomorphicSection (U : Set Q) (f : U → ℂ) : Prop := by
  classical
  exact ∀ z ∈ Set.range Bers,
    originalModuliAmbientProjection R hg hgenus hΓ hp z ∈ U →
      AnalyticAt ℂ (fun w =>
        if hw : originalModuliAmbientProjection R hg hgenus hΓ hp w ∈ U then
          f ⟨originalModuliAmbientProjection R hg hgenus hΓ hp w, hw⟩
        else 0) z

/-- Global representatives that are holomorphic on some actual neighborhood
of the given original moduli point. Only pointwise ring closure is used. -/
def originalModuliNearHolomorphicRing (m : Q) : Subring (Q → ℂ) := by
  letI : TopologicalSpace Q := CompactGenusModuliSpace.qcTopology R hg hgenus
  exact
    { carrier := {f | ∃ U : Set Q, IsOpen U ∧ m ∈ U ∧
        ∀ z ∈ Set.range Bers,
          originalModuliAmbientProjection R hg hgenus hΓ hp z ∈ U →
            AnalyticAt ℂ (f ∘ originalModuliAmbientProjection R hg hgenus hΓ hp) z}
      zero_mem' := by
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ m, ?_⟩
        intro z _ _
        exact analyticAt_const
      one_mem' := by
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ m, ?_⟩
        intro z _ _
        exact analyticAt_const
      add_mem' := by
        rintro f k ⟨U, hU, hmU, hf⟩ ⟨V, hV, hmV, hk⟩
        refine ⟨U ∩ V, hU.inter hV, ⟨hmU, hmV⟩, ?_⟩
        intro z hz hm
        exact (hf z hz hm.1).add (hk z hz hm.2)
      neg_mem' := by
        rintro f ⟨U, hU, hmU, hf⟩
        refine ⟨U, hU, hmU, ?_⟩
        intro z hz hm
        exact (hf z hz hm).neg
      mul_mem' := by
        rintro f k ⟨U, hU, hmU, hf⟩ ⟨V, hV, hmV, hk⟩
        refine ⟨U ∩ V, hU.inter hV, ⟨hmU, hmV⟩, ?_⟩
        intro z hz hm
        exact (hf z hz hm.1).mul (hk z hz hm.2) }

/-- The genuine point-germ ring: the image of locally holomorphic global
representatives in actual neighborhood germs on the original quotient. -/
def originalModuliHolomorphicGermRing (m : Q) :
    letI : TopologicalSpace Q := CompactGenusModuliSpace.qcTopology R hg hgenus
    Subring (Filter.Germ (𝓝 m) ℂ) := by
  letI : TopologicalSpace Q := CompactGenusModuliSpace.qcTopology R hg hgenus
  exact (originalModuliNearHolomorphicRing R hg hgenus hΓ hp m).map
    (Filter.Germ.coeRingHom (𝓝 m))

/-- A finite linear quotient chart must have a finite analytic zero-locus
realization and preserve all actual local holomorphic functions. -/
def HasOriginalModuliFiniteAnalyticChart (m : Q) : Prop := by
  letI : TopologicalSpace Q := CompactGenusModuliSpace.qcTopology R hg hgenus
  exact ∃ (U : Set Q) (_hU : IsOpen U) (hm : m ∈ U)
      (V : Set E) (_hV : IsOpen V) (hzero : (0 : E) ∈ V)
      (K : Subgroup (E ≃L[ℂ] E)) (q : V → U)
      (n r : ℕ) (W : Set (Fin n → ℂ))
      (F : (Fin n → ℂ) → Fin r → ℂ)
      (a : E → Fin n → ℂ)
      (e : U ≃ₜ {w : Fin n → ℂ | w ∈ W ∧ F w = 0}),
    (K : Set (E ≃L[ℂ] E)).Finite ∧
    (∀ k : K, Set.MapsTo (k : E ≃L[ℂ] E) V V) ∧
    Topology.IsQuotientMap q ∧ q ⟨0, hzero⟩ = ⟨m, hm⟩ ∧
    (∀ v w : V, q v = q w ↔ ∃ k : K, (k : E ≃L[ℂ] E) v.val = w.val) ∧
    IsOpen W ∧ AnalyticOnNhd ℂ F W ∧ AnalyticOnNhd ℂ a V ∧
    (∀ v : V, a v.val = (e (q v)).val) ∧
    ∀ (S : Set Q) (_hS : IsOpen S) (hSU : S ⊆ U) (f : S → ℂ),
      IsOriginalModuliHolomorphicSection R hg hgenus hΓ hp S f ↔
        ∀ x : S, ∃ (B : Set (Fin n → ℂ)) (H : (Fin n → ℂ) → ℂ),
          IsOpen B ∧ B ⊆ W ∧ (e ⟨x.val, hSU x.property⟩).val ∈ B ∧
          AnalyticOnNhd ℂ H B ∧
          ∀ y : S, (e ⟨y.val, hSU y.property⟩).val ∈ B →
            H (e ⟨y.val, hSU y.property⟩).val = f y

/-- Concrete normal analytic data on the original moduli carrier and topology.
The function sheaf and every analytic chart have exactly the specified
pullback sections. Normality and dimension concern their actual point germs. -/
def HasOriginalModuliNormalAnalyticPresentation : Prop := by
  letI : TopologicalSpace Q := CompactGenusModuliSpace.qcTopology R hg hgenus
  exact Topology.IsQuotientMap (originalModuliBersProjection R hg hgenus hΓ hp) ∧
    T2Space Q ∧ SecondCountableTopology Q ∧
    (∃ L : TopCat.LocalPredicate (fun _ : TopCat.of Q => ℂ),
      ∀ (U : TopologicalSpace.Opens (TopCat.of Q)) (f : U → ℂ),
        L.pred f ↔ IsOriginalModuliHolomorphicSection R hg hgenus hΓ hp (U : Set Q) f) ∧
    (∀ U : TopologicalSpace.Opens (TopCat.of Q),
      ∃ A : Subalgebra ℂ (U → ℂ), ∀ f : U → ℂ,
        f ∈ A ↔ IsOriginalModuliHolomorphicSection R hg hgenus hΓ hp (U : Set Q) f) ∧
    (∀ m : Q, HasOriginalModuliFiniteAnalyticChart R hg hgenus hΓ hp m) ∧
    ∀ m : Q,
      let A := originalModuliHolomorphicGermRing R hg hgenus hΓ hp m
      IsLocalRing A ∧ IsNoetherianRing A ∧
      ∃ hdom : IsDomain A,
        letI : IsDomain A := hdom
        IsIntegrallyClosed A ∧ ringKrullDim A = ((3 * g - 3 : ℕ) : WithBot ℕ∞)

end LowDimensionalTopology.Geometry.Teichmuller
