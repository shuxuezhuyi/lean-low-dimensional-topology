module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrum
public import LowDimensionalTopology.Geometry.Teichmuller.MappingClassGroup
public import LowDimensionalTopology.Geometry.Surfaces.SpectrumReindexing

/-!
# The marked-length equivariance step

The existing positive smooth mapping action on the original curve classes
gives the exact reindexing of the existing marked length function, rather
than postulating invariance of that function's image.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Homotopic original homeomorphisms induce the same original free-class
permutation. Free homotopies of curves need not stay embedded. -/
theorem essentialSimpleFreeClassEquiv_eq_of_homotopic
    {X : Type} [TopologicalSpace X] (h k : X ≃ₜ X)
    (H : ContinuousMap.Homotopic (_root_.toContinuousMap h) (_root_.toContinuousMap k)) :
    essentialSimpleFreeClassEquiv h = essentialSimpleFreeClassEquiv k := by
  apply Equiv.ext
  intro a
  refine Quotient.inductionOn a ?_
  intro c
  apply Quotient.sound
  exact Or.inl (H.comp (ContinuousMap.Homotopic.refl c.1))

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

/-- Precomposing the actual marking evaluates the unchanged marked spectrum on
the precisely postcomposed source class. The target complex surface is unchanged. -/
theorem markedLengthSpectrum_precompose
    (f : SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hf : PreservesComplexOrientation R.toRiemannAtlas R.toRiemannAtlas f.toHomeomorph)
    (t : TeichmullerSpace.{0, 0} R) (a : EssentialSimpleFreeClass X) :
    markedLengthSpectrum R hg hgenus (TeichmullerSpace.precompose f hf t) a =
      markedLengthSpectrum R hg hgenus t (essentialSimpleFreeClassEquiv f.toHomeomorph a) := by
  refine Quotient.inductionOn a ?_
  intro c
  change markedLengthSpectrum R hg hgenus (TeichmullerSpace.precompose f hf t) c.freeClass =
    markedLengthSpectrum R hg hgenus t (c.mapHomeomorph f.toHomeomorph).freeClass
  apply Subtype.ext
  rw [markedLengthSpectrum_apply, markedLengthSpectrum_apply]
  refine Quotient.inductionOn t ?_
  intro m
  change (markedLoopLength R hg hgenus (circleRepresentativeLoop c.1)
      (MarkedRiemannSurface.precompose f hf m)).toReal =
    (markedLoopLength R hg hgenus
      (circleRepresentativeLoop (c.mapHomeomorph f.toHomeomorph).1) m).toReal
  apply congrArg ENNReal.toReal
  exact LiZhongQC.s30b_fhl_congr _ (LiZhongQC.s30b_fh_of_eq (fun _ => rfl))

/-- Inverse precomposition agrees with the inverse-indexed product action at
every original curve class and every original marked point. -/
theorem markedLengthSpectrum_smul (f : OrientedSurfaceAut R)
    (t : TeichmullerSpace.{0, 0} R) :
    positiveSpectrumToNonnegative (markedLengthSpectrum R hg hgenus (f • t)) =
      nonnegativeSpectrumReindex (essentialSimpleFreeClassEquiv f.toHomeomorph)
        (positiveSpectrumToNonnegative (markedLengthSpectrum R hg hgenus t)) := by
  funext a
  apply Subtype.ext
  change (markedLengthSpectrum R hg hgenus (f • t) a : ℝ) =
    (markedLengthSpectrum R hg hgenus t
      ((essentialSimpleFreeClassEquiv f.toHomeomorph).symm a) : ℝ)
  exact congrArg (fun z : Set.Ioi (0 : ℝ) => (z : ℝ))
    (markedLengthSpectrum_precompose R hg hgenus (f⁻¹).smooth
      (f⁻¹).orientation_preserving t a)

/-- Include the complete actual marked length spectrum in the original
nonnegative cone with zero deleted. The supplied original class is used only
to witness nonvanishing, and no coordinate is omitted or normalized. -/
def nonzeroMarkedLengthSpectrum (a₀ : EssentialSimpleFreeClass X)
    (t : TeichmullerSpace.{0, 0} R) : NonzeroNonnegativeSpectrum X :=
  ⟨positiveSpectrumToNonnegative (markedLengthSpectrum R hg hgenus t), by
    intro hzero
    have ha : (markedLengthSpectrum R hg hgenus t a₀ : ℝ) = 0 :=
      congrArg (fun f : NonnegativeSpectrum X => (f a₀ : ℝ)) hzero
    exact (ne_of_gt (markedLengthSpectrum R hg hgenus t a₀).property) ha⟩

/-- The original complete marked-length ray in the literal projective
nonnegative spectrum space used for Thurston's boundary. -/
def projectiveMarkedLengthSpectrum (a₀ : EssentialSimpleFreeClass X)
    (t : TeichmullerSpace.{0, 0} R) : ProjectiveNonnegativeSpectrum X :=
  projectivizeNonnegativeSpectrum (nonzeroMarkedLengthSpectrum R hg hgenus a₀ t)

/-- The literal original projective action agrees with the existing marked
action before taking the closure. -/
theorem projectiveMarkedLengthSpectrum_smul (a₀ : EssentialSimpleFreeClass X)
    (f : OrientedSurfaceAut R) (t : TeichmullerSpace.{0, 0} R) :
    projectiveSpectrumHomeomorph f.toHomeomorph
        (projectiveMarkedLengthSpectrum R hg hgenus a₀ t) =
      projectiveMarkedLengthSpectrum R hg hgenus a₀ (f • t) := by
  change projectivizeNonnegativeSpectrum
      (nonzeroNonnegativeSpectrumReindex (essentialSimpleFreeClassEquiv f.toHomeomorph)
        (nonzeroMarkedLengthSpectrum R hg hgenus a₀ t)) =
    projectivizeNonnegativeSpectrum (nonzeroMarkedLengthSpectrum R hg hgenus a₀ (f • t))
  apply congrArg projectivizeNonnegativeSpectrum
  apply Subtype.ext
  exact (markedLengthSpectrum_smul R hg hgenus f t).symm

/-- The existing marked action and its actual inverse prove invariance of the
whole original projective marked-length image. -/
theorem projectiveSpectrumHomeomorph_image_markedLengthSpectrum
    (a₀ : EssentialSimpleFreeClass X) (f : OrientedSurfaceAut R) :
    projectiveSpectrumHomeomorph f.toHomeomorph ''
        Set.range (projectiveMarkedLengthSpectrum R hg hgenus a₀) =
      Set.range (projectiveMarkedLengthSpectrum R hg hgenus a₀) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
    exact ⟨f • t, (projectiveMarkedLengthSpectrum_smul R hg hgenus a₀ f t).symm⟩
  · rintro y ⟨t, rfl⟩
    refine ⟨projectiveMarkedLengthSpectrum R hg hgenus a₀ (f⁻¹ • t),
      ⟨f⁻¹ • t, rfl⟩, ?_⟩
    rw [projectiveMarkedLengthSpectrum_smul, smul_inv_smul]

end LowDimensionalTopology.Geometry.Teichmuller
