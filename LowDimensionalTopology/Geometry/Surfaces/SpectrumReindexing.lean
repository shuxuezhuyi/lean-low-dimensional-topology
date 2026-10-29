module

public import LowDimensionalTopology.Geometry.Surfaces.ProjectiveSpectra
public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleClassHomeomorph
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Reindexing the original nonnegative and projective spectra

The actual permutation of original simple free classes reindexes the
original product. Reindexing preserves its zero function and its common
positive-scaling relation, so it gives a homeomorphism of the existing
projective nonnegative spectrum space.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Reindex the literal nonnegative product by the inverse class permutation. -/
def nonnegativeSpectrumReindex
    (e : EssentialSimpleFreeClass X ≃ EssentialSimpleFreeClass Y) :
    NonnegativeSpectrum X ≃ₜ NonnegativeSpectrum Y where
  toFun f b := f (e.symm b)
  invFun f a := f (e a)
  left_inv f := by
    funext a
    exact congrArg f (e.symm_apply_apply a)
  right_inv f := by
    funext a
    exact congrArg f (e.apply_symm_apply a)
  continuous_toFun := continuous_pi (fun b => continuous_apply (e.symm b))
  continuous_invFun := continuous_pi (fun a => continuous_apply (e a))

/-- Zero is preserved, so restriction deletes exactly the same zero orbit. -/
def nonzeroNonnegativeSpectrumReindex
    (e : EssentialSimpleFreeClass X ≃ EssentialSimpleFreeClass Y) :
    NonzeroNonnegativeSpectrum X ≃ₜ NonzeroNonnegativeSpectrum Y :=
  (nonnegativeSpectrumReindex e).subtype (fun f => by
    constructor
    · intro hf hzero
      apply hf
      funext a
      change f a = 0
      have ha := congrFun hzero (e a)
      change f (e.symm (e a)) = 0 at ha
      simpa only [Equiv.symm_apply_apply] using ha
    · intro hf hzero
      apply hf
      rw [hzero]
      rfl)

/-- The same positive scalar witnesses projective equivalence after reindexing. -/
def projectiveNonnegativeSpectrumReindex
    (e : EssentialSimpleFreeClass X ≃ EssentialSimpleFreeClass Y) :
    ProjectiveNonnegativeSpectrum X ≃ₜ ProjectiveNonnegativeSpectrum Y :=
  Homeomorph.Quotient.congr (nonzeroNonnegativeSpectrumReindex e) (fun f g => by
    change (∃ c : ℝ, 0 < c ∧ ∀ a, (f.val a : ℝ) = c * (g.val a : ℝ)) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ b,
        (f.val (e.symm b) : ℝ) = c * (g.val (e.symm b) : ℝ)
    constructor
    · rintro ⟨c, hc, hfg⟩
      exact ⟨c, hc, fun b => hfg (e.symm b)⟩
    · rintro ⟨c, hc, hfg⟩
      refine ⟨c, hc, fun a => ?_⟩
      simpa only [Equiv.symm_apply_apply] using hfg (e a))

/-- Each original representative ray is sent to its precisely reindexed ray. -/
@[simp] theorem projectiveNonnegativeSpectrumReindex_projectivize
    (e : EssentialSimpleFreeClass X ≃ EssentialSimpleFreeClass Y)
    (f : NonzeroNonnegativeSpectrum X) :
    projectiveNonnegativeSpectrumReindex e (projectivizeNonnegativeSpectrum f) =
      projectivizeNonnegativeSpectrum (nonzeroNonnegativeSpectrumReindex e f) := rfl

/-- The actual projective spectrum homeomorphism induced by a given original
surface homeomorphism, with no realization or foliation conclusion assumed. -/
def projectiveSpectrumHomeomorph (h : X ≃ₜ Y) :
    ProjectiveNonnegativeSpectrum X ≃ₜ ProjectiveNonnegativeSpectrum Y :=
  projectiveNonnegativeSpectrumReindex (essentialSimpleFreeClassEquiv h)

end LowDimensionalTopology.Geometry.Surfaces
