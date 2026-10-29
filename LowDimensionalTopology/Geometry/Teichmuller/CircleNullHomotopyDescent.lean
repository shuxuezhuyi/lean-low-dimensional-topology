module

public import LowDimensionalTopology.Geometry.Teichmuller.CircleRepresentativeLoops
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Set Surfaces
open scoped unitInterval

/-- Free homotopy of the actual complete traversals is exactly homotopy of
the original circle maps, via the endpoint quotient of the unit interval. -/
theorem circleRepresentativeLoop_freelyHomotopic_iff
    {X : Type} [TopologicalSpace X] (f g : C(Circle, X)) :
    LiZhongQC.FreelyHomotopic (circleRepresentativeLoop f) (circleRepresentativeLoop g) ↔
      f.Homotopic g := by
  constructor
  · rintro ⟨H, h0, h1, hc⟩
    let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
    let J := Icc (0 : ℝ) (0 + 1)
    let κ : J → I := fun t => ⟨t.1, by simpa only [J, zero_add] using t.2⟩
    have hκ : Continuous κ := continuous_subtype_val.subtype_mk _
    let K : C(J × I, X) :=
      ⟨fun p => H (p.2, κ p.1),
        H.continuous.comp (continuous_snd.prodMk (hκ.comp continuous_fst))⟩
    let F : C(J, C(I, X)) := K.curry
    let Q := Quot (AddCircle.EndpointIdent (1 : ℝ) 0)
    let ψ : C(Q, C(I, X)) :=
      ⟨Quot.lift F (by
        rintro _ _ ⟨⟩
        ext s
        simpa [F, K, κ] using hc s), continuous_quot_lift _ F.continuous⟩
    let e : Circle ≃ₜ Q :=
      (AddCircle.homeomorphCircle (T := 1) one_ne_zero).symm.trans
        (AddCircle.homeoIccQuot (1 : ℝ) 0)
    let L : C(Circle, C(I, X)) := ψ.comp ⟨e, e.continuous⟩
    let D : C(I × Circle, X) :=
      ⟨fun p => L p.2 p.1, L.uncurry.continuous.comp continuous_swap⟩
    have hD (r : I) (k : C(Circle, X))
        (hr : ∀ t : I, H (r, t) = k (Circle.expLoop t)) :
        ∀ z, D (r, z) = k z := by
      intro z
      obtain ⟨q, rfl⟩ := e.symm.surjective z
      induction q using Quot.ind with
      | _ t =>
        change ψ (e (e.symm (Quot.mk _ t))) r = k (e.symm (Quot.mk _ t))
        rw [e.apply_symm_apply]
        change H (r, κ t) = k (e.symm (Quot.mk _ t))
        rw [hr]
        congr 1
        rw [Circle.expLoop_apply]
        change Circle.exp (2 * Real.pi * (κ t : ℝ)) =
          AddCircle.homeomorphCircle (T := 1) one_ne_zero (t.1 : AddCircle (1 : ℝ))
        rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
        simp [κ]
    exact ⟨⟨D, hD 0 f h0, hD 1 g h1⟩⟩
  · exact circleRepresentativeLoop_homotopic

/-- A free null homotopy of the actual once-around loop descends to the
original circle map, using only the actual endpoint quotient of [0,1]. -/
theorem circleRepresentativeLoop_null_iff {X : Type} [TopologicalSpace X]
    (f : C(Circle, X)) :
    IsNullHomotopicLoop (circleRepresentativeLoop f) ↔ f.Nullhomotopic := by
  constructor
  · rintro ⟨x, h⟩
    exact ⟨x, (circleRepresentativeLoop_freelyHomotopic_iff f
      (ContinuousMap.const Circle x)).mp h⟩
  · exact circleRepresentativeLoop_null_of_null

/-- The existing essential circle predicate implies the required loop predicate. -/
theorem essentialSimpleCircle_loop_not_null
    {X : Type} [TopologicalSpace X] (c : EssentialSimpleCircle X) :
    ¬ IsNullHomotopicLoop (circleRepresentativeLoop c.1) :=
  fun h => c.2.2 ((circleRepresentativeLoop_null_iff c.1).mp h)

end LowDimensionalTopology.Geometry.Teichmuller
