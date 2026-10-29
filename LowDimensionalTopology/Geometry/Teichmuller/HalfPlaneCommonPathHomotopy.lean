/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.GeneratorLoopTransport
public import LowDimensionalTopology.Geometry.Surfaces.Covering.UniversalDeck
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S23_QCOnSurfaces

/-!
# Common-path comparison on actual half-plane quotients

One common path transporting every induced fundamental-group class gives a
homotopy of the same original homeomorphisms. The converse follows from
the existing `GeneratorLoopTransport`; this proof uses the half-plane
homotopy criterion. Lifts are chosen at the endpoints of the same lifted
common path, and all deck comparisons use actual deck homeomorphisms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X Y : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [T2Space X] [ConnectedSpace X] [T2Space Y] [ConnectedSpace Y]

/-- One actual common basepoint path identifying all induced classes gives
a homotopy between the same homeomorphisms of the original uniformized
surfaces. The required homeomorphic lifts and their matching basepoints are
constructed from the two supplied uniformizations. -/
theorem homotopic_of_halfPlane_commonPath
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → X} {p₁ : UpperHalfPlane → Y}
    (hp₀ : LiZhongQC.IsUniformization Γ₀ p₀)
    (hp₁ : LiZhongQC.IsUniformization Γ₁ p₁)
    (f g : X ≃ₜ Y) (x : X) (c : Path (f x) (g x))
    (hAll : ∀ a : FundamentalGroup X x,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map (f : C(X, Y)) x a) =
          FundamentalGroup.map (g : C(X, Y)) x a) :
    ContinuousMap.Homotopic (f : C(X, Y)) (g : C(X, Y)) := by
  classical
  obtain ⟨τ₀, rfl⟩ := hp₀.2.2.1 x
  obtain ⟨u, hu⟩ := hp₁.2.2.1 (f (p₀ τ₀))
  obtain ⟨F, hF, _⟩ := LiZhongQC.exists_lift hp₀ hp₁ f τ₀ u hu
  let eF : p₁ ⁻¹' {f (p₀ τ₀)} := ⟨F τ₀, hF τ₀⟩
  let eG : p₁ ⁻¹' {g (p₀ τ₀)} :=
    hp₁.1.monodromy (Path.Homotopic.Quotient.mk c) eF
  obtain ⟨G, hG, hG₀⟩ := LiZhongQC.exists_lift hp₀ hp₁ g τ₀ eG.val eG.property
  let q := covering_deck_isQuotientCoveringMap hp₁.1 hp₁.2.2.1
  apply (LiZhongQC.thm23_1_homotopy_iff hp₀ hp₁ f g hF hG).mpr
  refine ⟨1, Γ₁.one_mem, ?_⟩
  intro γ hγ τ
  simp only [inv_one, one_smul]
  have hpγ (z : UpperHalfPlane) : p₀ (γ • z) = p₀ z :=
    ((hp₀.2.2.2 z (γ • z)).2 ⟨γ, hγ, rfl⟩).symm
  let L : Path τ₀ (γ • τ₀) := PathConnectedSpace.somePath τ₀ (γ • τ₀)
  let l : Path (p₀ τ₀) (p₀ τ₀) :=
    (L.map hp₀.1.continuous).cast rfl (hpγ τ₀).symm
  let eF' : p₁ ⁻¹' {f (p₀ τ₀)} :=
    ⟨F (γ • τ₀), (hF _).trans (congrArg f (hpγ τ₀))⟩
  let eG' : p₁ ⁻¹' {g (p₀ τ₀)} :=
    ⟨G (γ • τ₀), (hG _).trans (congrArg g (hpγ τ₀))⟩
  have hFm : hp₁.1.monodromy
      (Path.Homotopic.Quotient.mk (l.map f.continuous)) eF = eF' := by
    apply Subtype.ext
    calc
      _ = F (L 1) := hp₁.1.monodromy_eq_apply_one
        (e := eF) (Γ := (L.map F.continuous).toContinuousMap)
        (by funext t; exact hF (L t)) (congrArg F L.source)
      _ = F (γ • τ₀) := congrArg F L.target
  have hGm : hp₁.1.monodromy
      (Path.Homotopic.Quotient.mk (l.map g.continuous)) eG = eG' := by
    apply Subtype.ext
    calc
      _ = G (L 1) := hp₁.1.monodromy_eq_apply_one
        (e := eG) (Γ := (L.map G.continuous).toContinuousMap)
        (by funext t; exact hG (L t)) ((congrArg G L.source).trans hG₀)
      _ = G (γ • τ₀) := congrArg G L.target
  have hpFγ : p₁ (F τ₀) = p₁ (F (γ • τ₀)) :=
    (hF τ₀).trans (((hF (γ • τ₀)).trans (congrArg f (hpγ τ₀))).symm)
  obtain ⟨d, hd⟩ := covering_exists_deck_map hp₁.1 (F τ₀) (F (γ • τ₀)) hpFγ
  have hdF : q.toPermFiber (f (p₀ τ₀)) d eF = eF' := Subtype.ext hd
  have hs : Path.Homotopic ((l.map f.continuous).trans c)
      (c.trans (l.map g.continuous)) :=
    (basedLoop_transport_iff (f : C(X, Y)) (g : C(X, Y)) (p₀ τ₀) c l).mp
      (hAll (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk l)))
  have hsq :
      (Path.Homotopic.Quotient.mk (l.map f.continuous)).trans
          (Path.Homotopic.Quotient.mk c) =
        (Path.Homotopic.Quotient.mk c).trans
          (Path.Homotopic.Quotient.mk (l.map g.continuous)) := by
    simpa only [Path.Homotopic.Quotient.mk_trans] using
      (Path.Homotopic.Quotient.eq.mpr hs)
  have hend : q.toPermFiber (g (p₀ τ₀)) d eG = eG' := by
    calc
      _ = hp₁.1.monodromy (Path.Homotopic.Quotient.mk c)
          (q.toPermFiber (f (p₀ τ₀)) d eF) :=
        (q.monodromy_toPermFiber (g := d)
          (γ := Path.Homotopic.Quotient.mk c) (e := eF)).symm
      _ = hp₁.1.monodromy (Path.Homotopic.Quotient.mk c) eF' := by rw [hdF]
      _ = hp₁.1.monodromy
          ((Path.Homotopic.Quotient.mk (l.map f.continuous)).trans
            (Path.Homotopic.Quotient.mk c)) eF := by
        rw [IsCoveringMap.monodromy_trans_apply, hFm]
      _ = hp₁.1.monodromy
          ((Path.Homotopic.Quotient.mk c).trans
            (Path.Homotopic.Quotient.mk (l.map g.continuous))) eF := by rw [hsq]
      _ = eG' := by
        rw [IsCoveringMap.monodromy_trans_apply]
        exact hGm
  have hdG : d • G τ₀ = G (γ • τ₀) :=
    (congrArg (fun z : UpperHalfPlane => d • z) hG₀).trans
      (congrArg Subtype.val hend)
  have hDF : (fun z => F (γ • F.symm z)) = fun z => d • z := by
    refine hp₁.1.eq_of_comp_eq
      (F.continuous.comp ((continuous_const_smul γ).comp F.symm.continuous))
      (continuous_const_smul d) ?_ (F τ₀) ?_
    · funext z
      calc
        p₁ (F (γ • F.symm z)) = f (p₀ (γ • F.symm z)) := hF _
        _ = f (p₀ (F.symm z)) := congrArg f (hpγ _)
        _ = p₁ (F (F.symm z)) := (hF _).symm
        _ = p₁ z := congrArg p₁ (F.apply_symm_apply z)
        _ = p₁ (d • z) := (deck.proj_smul d z).symm
    · simpa only [F.symm_apply_apply] using hd.symm
  have hDG : (fun z => G (γ • G.symm z)) = fun z => d • z := by
    refine hp₁.1.eq_of_comp_eq
      (G.continuous.comp ((continuous_const_smul γ).comp G.symm.continuous))
      (continuous_const_smul d) ?_ (G τ₀) ?_
    · funext z
      calc
        p₁ (G (γ • G.symm z)) = g (p₀ (γ • G.symm z)) := hG _
        _ = g (p₀ (G.symm z)) := congrArg g (hpγ _)
        _ = p₁ (G (G.symm z)) := (hG _).symm
        _ = p₁ z := congrArg p₁ (G.apply_symm_apply z)
        _ = p₁ (d • z) := (deck.proj_smul d z).symm
    · simpa only [G.symm_apply_apply] using hdG.symm
  exact congrFun (hDF.trans hDG.symm) τ

end LowDimensionalTopology.Geometry.Teichmuller
