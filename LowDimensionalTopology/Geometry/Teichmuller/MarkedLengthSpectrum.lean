module

public import LowDimensionalTopology.Geometry.Teichmuller.CircleNullHomotopyDescent
public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLengthReversal
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLength

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

/-- Reversing the actual circle is the actual reverse of its full once-around loop. -/
theorem circleRepresentativeLoop_reverse {X : Type} [TopologicalSpace X]
    (f : C(Circle, X)) :
    LiZhongQC.FreelyHomotopic (circleRepresentativeLoop (f.comp circleReversal))
      ⟨(circleRepresentativeLoop f).1, (circleRepresentativeLoop f).2.symm⟩ := by
  apply LiZhongQC.s30b_fh_of_eq
  intro t
  change f ((Circle.expLoop t)⁻¹) = f (Circle.expLoop (unitInterval.symm t))
  rw [Circle.expLoop_apply, Circle.expLoop_apply, unitInterval.coe_symm_eq]
  congr 1
  rw [← Circle.exp_neg,
    show 2 * Real.pi * (1 - (t : ℝ)) = -(2 * Real.pi * (t : ℝ)) + 2 * Real.pi by ring,
    Circle.exp_add]
  simp

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

private theorem markedCircleLength_loop_congr {α β : LiZhongQC.Loop X}
    (h : LiZhongQC.FreelyHomotopic α β) (t : TeichmullerSpace.{0, 0} R) :
    markedGeodesicLength R hg hgenus α t = markedGeodesicLength R hg hgenus β t := by
  refine Quotient.inductionOn t ?_
  intro m
  exact congrArg ENNReal.toReal (LiZhongQC.s30b_fhl_congr _
    (LiZhongQC.s30b_fh_map m.markingMap.continuous h))

/-- The native marked value forgets the source circle's orientation. -/
theorem markedGeodesicLength_circle_reverse (f : C(Circle, X))
    (t : TeichmullerSpace.{0, 0} R) :
    markedGeodesicLength R hg hgenus (circleRepresentativeLoop (f.comp circleReversal)) t =
      markedGeodesicLength R hg hgenus (circleRepresentativeLoop f) t :=
  (markedCircleLength_loop_congr R hg hgenus (circleRepresentativeLoop_reverse f) t).trans
    (markedGeodesicLength_reverse R hg hgenus (circleRepresentativeLoop f) t)

/-- The whole positive marked length spectrum, indexed by the original
essential unoriented simple free classes, at every original marked point. -/
def markedLengthSpectrum (t : TeichmullerSpace.{0, 0} R) : PositiveSpectrum X :=
  fun a => Quotient.lift
    (fun c : EssentialSimpleCircle X =>
      (⟨markedGeodesicLength R hg hgenus (circleRepresentativeLoop c.1) t,
        markedGeodesicLength_pos R hg hgenus (circleRepresentativeLoop c.1)
          (essentialSimpleCircle_loop_not_null c) t⟩ : Set.Ioi (0 : ℝ)))
    (by
      intro c d h
      apply Subtype.ext
      rcases h with h | h
      · exact markedGeodesicLength_circleRepresentative_homotopic R hg hgenus h t
      · exact (markedGeodesicLength_circleRepresentative_homotopic R hg hgenus h t).trans
          (markedGeodesicLength_circle_reverse R hg hgenus d.1 t)) a

/-- A representative of any actual source class gives its original marked value. -/
theorem markedLengthSpectrum_apply (t : TeichmullerSpace.{0, 0} R)
    (c : EssentialSimpleCircle X) :
    (markedLengthSpectrum R hg hgenus t c.freeClass : ℝ) =
      markedGeodesicLength R hg hgenus (circleRepresentativeLoop c.1) t := rfl

/-- On any actual model of the same marked target, each spectrum coordinate
is the same original geodesic's complete BV length. -/
theorem markedLengthSpectrum_mk_eq (c : EssentialSimpleCircle X)
    (m : MarkedRiemannSurface.{0, 0} R) (M : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (q : OriginalClosedGeodesic M)
    (hq : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap (circleRepresentativeLoop c.1).1,
        (circleRepresentativeLoop c.1).2.map m.markingMap.continuous⟩ q.toLoop) :
    (markedLengthSpectrum R hg hgenus (TeichmullerSpace.mk m) c.freeClass : ℝ) =
      q.length.toReal :=
  markedGeodesicLength_mk_eq R hg hgenus (circleRepresentativeLoop c.1) m M q hq

variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R
  (Nat.lt_of_succ_le hg) e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- The same complete positive spectrum on the whole literal native Fricke image. -/
def frickeMarkedLengthSpectrum (t : nativeFrickeImage hA) : PositiveSpectrum X :=
  letI := nativeFrickeTopology hA
  markedLengthSpectrum R hg hgenus ((nativeFrickeHomeomorph hA hAlt).symm t)

/-- The original literal coordinate vector has the same full-period BV coordinate. -/
theorem frickeMarkedLengthSpectrum_coordinates_eq (c : EssentialSimpleCircle X)
    (m : MarkedRiemannSurface.{0, 0} R) (M : HyperbolicSurfaceModel m.surface.toRiemannSurface)
    (q : OriginalClosedGeodesic M)
    (hq : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap (circleRepresentativeLoop c.1).1,
        (circleRepresentativeLoop c.1).2.map m.markingMap.continuous⟩ q.toLoop) :
    (frickeMarkedLengthSpectrum R hg hgenus hA hAlt
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ c.freeClass : ℝ) = q.length.toReal := by
  let := nativeFrickeTopology hA
  change frickeGeodesicLength R (Nat.lt_of_succ_le hg) hgenus hA hAlt
    (circleRepresentativeLoop c.1) _ = q.length.toReal
  exact frickeGeodesicLength_coordinates_eq R (Nat.lt_of_succ_le hg) hgenus hA hAlt
    (circleRepresentativeLoop c.1) m M q hq

end LowDimensionalTopology.Geometry.Teichmuller
