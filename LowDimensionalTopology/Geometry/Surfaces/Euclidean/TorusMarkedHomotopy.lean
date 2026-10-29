module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.NormalizedOrderedMarkedTorus
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Algebra.Ring.Periodic

/-!
# Homotopy of actual maps between period-lattice tori

The two original basis loops determine the homotopy class of every continuous
map between the genuine torus models. Both maps and the one common path which
transports their basepoints are actual maps and paths on those tori.
-/

@[expose] public section
noncomputable section

open Set Module
open scoped unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces.ComplexTorusModel

variable {b c : Basis (Fin 2) ℝ ℂ}

/-- A continuous plane lift has a constant displacement under each original
lattice period. The displacement is derived from covering uniqueness. -/
theorem continuous_lift_add_period
    (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (f : C(ComplexTorusCarrier, ComplexTorusCarrier)) (F : C(ℂ, ℂ))
    (hF : U.projection ∘ F = f ∘ T.projection)
    (v : ℂ) (hv : v ∈ Submodule.span ℤ (Set.range b)) (z : ℂ) :
    F (z + v) = F z + (F v - F 0) := by
  have hTv : T.projection v = T.projection 0 :=
    (T.fiber_iff v 0).mpr (by simpa only [sub_zero] using hv)
  have hδ : F v - F 0 ∈ Submodule.span ℤ (Set.range c) := by
    apply (U.fiber_iff (F v) (F 0)).mp
    exact (congrFun hF v).trans ((congrArg f hTv).trans (congrFun hF 0).symm)
  have heq : (fun w : ℂ => F (w + v)) = (fun w => F w + (F v - F 0)) := by
    apply U.covering.eq_of_comp_eq
      (F.continuous.comp (continuous_id.add continuous_const))
      (F.continuous.add continuous_const) ?_ 0 ?_
    · funext w
      change U.projection (F (w + v)) = U.projection (F w + (F v - F 0))
      rw [U.projection_add_period _ _ hδ]
      calc
        U.projection (F (w + v)) = f (T.projection (w + v)) := congrFun hF (w + v)
        _ = f (T.projection w) := congrArg f (T.projection_add_period w v hv)
        _ = U.projection (F w) := (congrFun hF w).symm
    · change F (0 + v) = F 0 + (F v - F 0)
      rw [zero_add]
      abel
  exact congrFun heq z

/-- Transporting the image of one original period loop through a common path
forces the two continuous lifts to have the same period displacement. -/
theorem lift_displacement_eq_of_transported_loop
    (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (f g : C(ComplexTorusCarrier, ComplexTorusCarrier)) (F G : C(ℂ, ℂ))
    (hF : U.projection ∘ F = f ∘ T.projection)
    (hG : U.projection ∘ G = g ∘ T.projection)
    (v : ℂ) (hv : v ∈ Submodule.span ℤ (Set.range b))
    (C₀ : Path (f (T.projection 0)) (g (T.projection 0)))
    (hmark : Path.Homotopic
      (((T.periodLoop v hv).map f.continuous).trans C₀)
      (C₀.trans ((T.periodLoop v hv).map g.continuous))) :
    F v - F 0 = G v - G 0 := by
  let e : U.projection ⁻¹' {f (T.projection 0)} := ⟨F 0, congrFun hF 0⟩
  let L₁ : C(I, ℂ) := ⟨fun t => F (t.val • v), by fun_prop⟩
  have hL₁ : U.projection ∘ L₁ = (T.periodLoop v hv).map f.continuous := by
    funext t
    exact congrFun hF (t.val • v)
  let e₁ := U.covering.monodromy
    (Path.Homotopic.Quotient.mk ((T.periodLoop v hv).map f.continuous)) e
  have he₁ : (e₁ : ℂ) = F v := by
    have h := U.covering.monodromy_eq_apply_one (e := e) (Γ := L₁)
      hL₁ (by simp [L₁, e])
    simpa only [L₁, ContinuousMap.coe_mk, Set.Icc.coe_one, one_smul] using h
  obtain ⟨C, hC, hC₀⟩ := U.covering.exists_path_lifts
    (C₀ : C(I, ComplexTorusCarrier)) (F 0)
    (C₀.source.trans (congrFun hF 0).symm)
  let eC := U.covering.monodromy (Path.Homotopic.Quotient.mk C₀) e
  have heC : (eC : ℂ) = C 1 := U.covering.monodromy_eq_apply_one hC hC₀
  have heCperiod : (eC : ℂ) - G 0 ∈ Submodule.span ℤ (Set.range c) := by
    apply (U.fiber_iff (eC : ℂ) (G 0)).mp
    exact eC.property.trans (congrFun hG 0).symm
  let L₂ : C(I, ℂ) :=
    ⟨fun t => G (t.val • v) + ((eC : ℂ) - G 0), by fun_prop⟩
  have hL₂ : U.projection ∘ L₂ = (T.periodLoop v hv).map g.continuous := by
    funext t
    exact (U.projection_add_period (G (t.val • v)) _ heCperiod).trans
      (congrFun hG (t.val • v))
  have hmon₂ :
      (U.covering.monodromy
        (Path.Homotopic.Quotient.mk ((T.periodLoop v hv).map g.continuous)) eC : ℂ) =
      G v + ((eC : ℂ) - G 0) := by
    have h := U.covering.monodromy_eq_apply_one (e := eC) (Γ := L₂)
      hL₂ (by
        change G ((0 : ℝ) • v) + ((eC : ℂ) - G 0) = (eC : ℂ)
        simp only [zero_smul]
        abel)
    simpa only [L₂, ContinuousMap.coe_mk, Set.Icc.coe_one, one_smul] using h
  have hδ : F v - F 0 ∈ Submodule.span ℤ (Set.range c) := by
    apply (U.fiber_iff (F v) (F 0)).mp
    have hTv : T.projection v = T.projection 0 :=
      (T.fiber_iff v 0).mpr (by simpa only [sub_zero] using hv)
    exact (congrFun hF v).trans ((congrArg f hTv).trans (congrFun hF 0).symm)
  let C' : C(I, ℂ) := ⟨fun t => C t + (F v - F 0), C.continuous.add continuous_const⟩
  have hC' : U.projection ∘ C' = C₀ := by
    funext t
    exact (U.projection_add_period (C t) _ hδ).trans (congrFun hC t)
  have hC'₀ : C' 0 = (e₁ : ℂ) := by
    change C 0 + (F v - F 0) = (e₁ : ℂ)
    rw [hC₀, he₁]
    abel
  have hmonC' :
      (U.covering.monodromy (Path.Homotopic.Quotient.mk C₀) e₁ : ℂ) =
      C 1 + (F v - F 0) := U.covering.monodromy_eq_apply_one hC' hC'₀
  have hpaths := Path.Homotopic.Quotient.eq.mpr hmark
  have hend := congrArg
    (fun P : Path.Homotopic.Quotient (f (T.projection 0)) (g (T.projection 0)) =>
      (U.covering.monodromy P e : ℂ)) hpaths
  simp only [Path.Homotopic.Quotient.mk_trans, U.covering.monodromy_trans_apply] at hend
  change (U.covering.monodromy (Path.Homotopic.Quotient.mk C₀) e₁ : ℂ) =
    (U.covering.monodromy
      (Path.Homotopic.Quotient.mk ((T.periodLoop v hv).map g.continuous)) eC : ℂ) at hend
  rw [hmonC', hmon₂, ← heC] at hend
  apply add_left_cancel (a := (eC : ℂ))
  calc
    (eC : ℂ) + (F v - F 0) = G v + ((eC : ℂ) - G 0) := hend
    _ = (eC : ℂ) + (G v - G 0) := by abel

/-- Equality of the two actual basis displacements descends the literal straight
line homotopy on the original covering plane. No lift is assumed equivariant. -/
theorem homotopic_of_lift_basis_displacements
    (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (f g : C(ComplexTorusCarrier, ComplexTorusCarrier)) (F G : C(ℂ, ℂ))
    (hF : U.projection ∘ F = f ∘ T.projection)
    (hG : U.projection ∘ G = g ∘ T.projection)
    (hdispl : ∀ i : Fin 2, F (b i) - F 0 = G (b i) - G 0) :
    ContinuousMap.Homotopic f g := by
  let D : ℂ → ℂ := fun z => G z - F z
  let P : Submodule ℤ ℂ :=
    { carrier := {v | Function.Periodic D v}
      zero_mem' := by intro z; simp
      add_mem' := fun hx hy => hx.add_period hy
      smul_mem' := fun n _ hx => hx.zsmul n }
  have hbP : Set.range b ⊆ P := by
    rintro _ ⟨i, rfl⟩ z
    have hv : b i ∈ Submodule.span ℤ (Set.range b) :=
      Submodule.subset_span (Set.mem_range_self i)
    change G (z + b i) - F (z + b i) = G z - F z
    rw [T.continuous_lift_add_period U f F hF (b i) hv z,
      T.continuous_lift_add_period U g G hG (b i) hv z, hdispl i]
    abel
  have hspan : Submodule.span ℤ (Set.range b) ≤ P := Submodule.span_le.mpr hbP
  have hD (z w : ℂ) (hzw : T.projection z = T.projection w) : D z = D w := by
    have hp : Function.Periodic D (z - w) := hspan ((T.fiber_iff z w).mp hzw)
    have hwz : w + (z - w) = z := by abel
    simpa only [hwz] using hp w
  let H₀ : I × ℂ → ℂ := fun p => F p.2 + p.1.val • D p.2
  let H : I × ComplexTorusCarrier → ComplexTorusCarrier := fun p =>
    U.projection (H₀ (p.1, Function.surjInv T.surjective p.2))
  have hHfiber (t : I) (z w : ℂ) (hzw : T.projection z = T.projection w) :
      U.projection (H₀ (t, z)) = U.projection (H₀ (t, w)) := by
    apply (U.fiber_iff _ _).mpr
    have hm : F z - F w ∈ Submodule.span ℤ (Set.range c) := by
      apply (U.fiber_iff _ _).mp
      exact (congrFun hF z).trans ((congrArg f hzw).trans (congrFun hF w).symm)
    have hdiff : H₀ (t, z) - H₀ (t, w) = F z - F w := by
      dsimp only [H₀]
      rw [hD z w hzw]
      abel
    rwa [hdiff]
  have hHcomm (t : I) (z : ℂ) : H (t, T.projection z) = U.projection (H₀ (t, z)) :=
    hHfiber t _ z (Function.surjInv_eq T.surjective (T.projection z))
  have hHc : Continuous H := by
    have hT : IsOpenQuotientMap T.projection :=
      ⟨T.surjective, T.covering.continuous, T.covering.isOpenMap⟩
    apply (IsOpenQuotientMap.id.prodMap hT).isQuotientMap.continuous_iff.mpr
    have heq : H ∘ Prod.map id T.projection = U.projection ∘ H₀ := by
      funext p
      exact hHcomm p.1 p.2
    rw [heq]
    exact U.covering.continuous.comp (by dsimp only [H₀, D]; fun_prop)
  refine ⟨{ toFun := H, continuous_toFun := hHc, map_zero_left := ?_, map_one_left := ?_ }⟩
  · intro x
    obtain ⟨z, rfl⟩ := T.surjective x
    rw [hHcomm]
    simpa only [H₀, Set.Icc.coe_zero, zero_smul, add_zero, Function.comp_apply]
      using congrFun hF z
  · intro x
    obtain ⟨z, rfl⟩ := T.surjective x
    rw [hHcomm]
    have hHone : H₀ (1, z) = G z := by
      dsimp only [H₀, D]
      simp only [Set.Icc.coe_one, one_smul]
      abel
    rw [hHone]
    exact congrFun hG z

/-- The genuine ordered basis loops classify all continuous torus maps up to
homotopy, with exactly one common path for the book's basepoint transport. -/
theorem homotopic_iff_transported_basis_loops
    (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (f g : C(ComplexTorusCarrier, ComplexTorusCarrier)) :
    ContinuousMap.Homotopic f g ↔
      ∃ C₀ : Path (f (T.projection 0)) (g (T.projection 0)),
        ∀ i : Fin 2, Path.Homotopic
          (((T.periodLoop (b i) (Submodule.subset_span (Set.mem_range_self i))).map
            f.continuous).trans C₀)
          (C₀.trans ((T.periodLoop (b i) (Submodule.subset_span
            (Set.mem_range_self i))).map g.continuous)) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨H.evalAt (T.projection 0), fun i => Path.Homotopic.map_trans_evalAt H _⟩
  · rintro ⟨C₀, hC₀⟩
    obtain ⟨w, hw⟩ := U.surjective (f (T.projection 0))
    obtain ⟨F, ⟨_hF₀, hF⟩, _⟩ := U.covering.existsUnique_continuousMap_lifts
      (f.comp ⟨T.projection, T.covering.continuous⟩) 0 w hw
    obtain ⟨v, hv⟩ := U.surjective (g (T.projection 0))
    obtain ⟨G, ⟨_hG₀, hG⟩, _⟩ := U.covering.existsUnique_continuousMap_lifts
      (g.comp ⟨T.projection, T.covering.continuous⟩) 0 v hv
    exact T.homotopic_of_lift_basis_displacements U f g F G hF hG (fun i =>
      T.lift_displacement_eq_of_transported_loop U f g F G hF hG (b i)
        (Submodule.subset_span (Set.mem_range_self i)) C₀ (hC₀ i))

end LowDimensionalTopology.Geometry.Surfaces.ComplexTorusModel
