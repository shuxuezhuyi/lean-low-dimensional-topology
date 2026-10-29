module

public import LowDimensionalTopology.Unproved.Surfaces.GenusComparison
public import LowDimensionalTopology.External.Jacobians.RiemannRoch
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Riemann–Roch for closed Riemann surfaces

The analytic theorem gives a genuine canonical divisor on the original complex
atlas. Its formulation with the topological handle genus explicitly requires
the outstanding comparison between analytic and topological genus.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A canonical divisor is the order divisor of a nonzero meromorphic one-form
on the actual complex atlas of the closed Riemann surface. -/
def IsCanonicalDivisor (R : ClosedRiemannSurface X) (K : Jacobians.Divisor X) : Prop :=
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  ∃ ω₀ : Jacobians.Dolbeault.MeromorphicOneForm X,
    (∃ x, ω₀.formOrderW x ≠ ⊤) ∧ ∀ x, ω₀.formOrderW x = (K x : WithTop ℤ)

/-- Analytic Riemann–Roch with the canonical form and its actual divisor retained. -/
theorem exists_canonicalData_riemannRoch (R : ClosedRiemannSurface X) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∃ data : Jacobians.Dolbeault.CanonicalForm17Data X, ∀ D : Jacobians.Divisor X,
      (Jacobians.lDim D : ℤ) - (Jacobians.lDim (data.K - D) : ℤ) =
        Jacobians.Divisor.deg X D + 1 - (_root_.genus X : ℤ) := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨_D, f, _hfmem, hf⟩ := Jacobians.Dolbeault.exists_nonconstant_meromorphic (X := X)
  let K := Jacobians.LaurentTail.pairCanonicalDivisor f hf
  let data := Jacobians.Dolbeault.canonicalForm17DataOfDivisor f hf K
    (Jacobians.LaurentTail.formOrderW_pairCanonicalDivisor f hf)
  refine ⟨data, fun D => ?_⟩
  change (Jacobians.lDim D : ℤ) - (Jacobians.lDim (K - D) : ℤ) =
    Jacobians.Divisor.deg X D + 1 - (_root_.genus X : ℤ)
  have hRR := Jacobians.LaurentTail.riemannRoch_tailForm (X := X) D
  rw [Jacobians.LaurentTail.h1TailDim_eq_lDim_pairCanonical_sub f hf D,
    Jacobians.LaurentTail.h1TailDim_zero_eq_genus_unconditional] at hRR
  exact hRR

/-- Analytic Riemann–Roch holds for every divisor of an actual nonzero
meromorphic one-form, rather than only for a chosen canonical representative. -/
theorem riemannRoch_of_isCanonicalDivisor_analytic (R : ClosedRiemannSurface X)
    {K : Jacobians.Divisor X} (hK : R.IsCanonicalDivisor K) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∀ D : Jacobians.Divisor X,
      (Jacobians.lDim D : ℤ) - (Jacobians.lDim (K - D) : ℤ) =
        Jacobians.Divisor.deg X D + 1 - (_root_.genus X : ℤ) := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  dsimp only
  obtain ⟨ω₀, hω₀, horder⟩ := hK
  let data : Jacobians.Dolbeault.CanonicalForm17Data X :=
    { ω₀ := ω₀, nontrivial := hω₀, K := K, order_eq := horder }
  obtain ⟨data₀, hRR⟩ := R.exists_canonicalData_riemannRoch
  intro D
  have hdata : Jacobians.lDim (K - D) = Jacobians.Dolbeault.omegaDim (-D) := by
    rw [sub_eq_add_neg, add_comm]
    exact data.lDim_add_K_eq_omegaDim (-D)
  have hdata₀ : Jacobians.lDim (data₀.K - D) = Jacobians.Dolbeault.omegaDim (-D) := by
    rw [sub_eq_add_neg, add_comm]
    exact data₀.lDim_add_K_eq_omegaDim (-D)
  rw [hdata.trans hdata₀.symm]
  exact hRR D

/-- Riemann–Roch for any actual canonical divisor, with the topological genus
and its analytic comparison supplied explicitly. -/
theorem riemannRoch_of_isCanonicalDivisor (R : ClosedRiemannSurface X)
    {K : Jacobians.Divisor X} (hK : R.IsCanonicalDivisor K) {g : ℕ}
    (hcomparison : Unproved.Surfaces.GenusComparison R g) (hgenus : R.HasGenus g) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∀ D : Jacobians.Divisor X,
      (Jacobians.lDim D : ℤ) - (Jacobians.lDim (K - D) : ℤ) =
        Jacobians.Divisor.deg X D + 1 - (g : ℤ) := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hg : _root_.genus X = g := hcomparison hgenus
  simpa only [hg] using R.riemannRoch_of_isCanonicalDivisor_analytic hK

/-- Every actual canonical divisor has degree twice the analytic genus minus
two, and its linear system has dimension equal to that genus. -/
theorem degree_of_isCanonicalDivisor_analytic (R : ClosedRiemannSurface X)
    {K : Jacobians.Divisor X} (hK : R.IsCanonicalDivisor K) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    Jacobians.Divisor.deg X K = 2 * (_root_.genus X : ℤ) - 2 ∧
      Jacobians.lDim K = _root_.genus X := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hRR := R.riemannRoch_of_isCanonicalDivisor_analytic hK
  exact ⟨Jacobians.deg_canonical hRR, Jacobians.lDim_canonical_eq_genus hRR⟩

/-- The degree and dimension of any actual canonical divisor, with the
comparison to the topological handle genus supplied explicitly. -/
theorem degree_of_isCanonicalDivisor (R : ClosedRiemannSurface X)
    {K : Jacobians.Divisor X} (hK : R.IsCanonicalDivisor K) {g : ℕ}
    (hcomparison : Unproved.Surfaces.GenusComparison R g) (hgenus : R.HasGenus g) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    Jacobians.Divisor.deg X K = 2 * (g : ℤ) - 2 ∧ Jacobians.lDim K = g := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hg : _root_.genus X = g := hcomparison hgenus
  simpa only [hg] using R.degree_of_isCanonicalDivisor_analytic hK

/-- Riemann–Roch with topological genus, conditional only on its comparison with
analytic genus. The divisor returned is that of an actual nonzero meromorphic form. -/
theorem exists_canonical_divisor_riemannRoch (R : ClosedRiemannSurface X) {g : ℕ}
    (hcomparison : Unproved.Surfaces.GenusComparison R g) (hgenus : R.HasGenus g) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∃ K : Jacobians.Divisor X, R.IsCanonicalDivisor K ∧ ∀ D : Jacobians.Divisor X,
      (Jacobians.lDim D : ℤ) - (Jacobians.lDim (K - D) : ℤ) =
        Jacobians.Divisor.deg X D + 1 - (g : ℤ) := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hg : _root_.genus X = g := hcomparison hgenus
  obtain ⟨data, hRR⟩ := R.exists_canonicalData_riemannRoch
  refine ⟨data.K, ⟨data.ω₀, data.nontrivial, data.order_eq⟩, fun D => ?_⟩
  simpa only [hg] using hRR D

/-- There is an actual canonical divisor of degree twice the analytic genus
minus two. Its linear system has dimension equal to the analytic genus. -/
theorem exists_canonical_divisor_degree_analytic (R : ClosedRiemannSurface X) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∃ K : Jacobians.Divisor X, R.IsCanonicalDivisor K ∧
      Jacobians.Divisor.deg X K = 2 * (_root_.genus X : ℤ) - 2 ∧
      Jacobians.lDim K = _root_.genus X := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨data, hRR⟩ := R.exists_canonicalData_riemannRoch
  exact ⟨data.K, ⟨data.ω₀, data.nontrivial, data.order_eq⟩,
    Jacobians.deg_canonical hRR, Jacobians.lDim_canonical_eq_genus hRR⟩

/-- The canonical degree and dimension stated with the actual topological handle
genus, with its comparison to analytic genus supplied explicitly. -/
theorem exists_canonical_divisor_degree (R : ClosedRiemannSurface X) {g : ℕ}
    (hcomparison : Unproved.Surfaces.GenusComparison R g) (hgenus : R.HasGenus g) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∃ K : Jacobians.Divisor X, R.IsCanonicalDivisor K ∧
      Jacobians.Divisor.deg X K = 2 * (g : ℤ) - 2 ∧ Jacobians.lDim K = g := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hg : _root_.genus X = g := hcomparison hgenus
  simpa only [hg] using R.exists_canonical_divisor_degree_analytic

/-- A linear system of negative degree contains only functions whose meromorphic
germ is zero everywhere. Point values of unrepaired representatives are irrelevant. -/
theorem germ_zero_of_mem_linearSystem_of_degree_neg (R : ClosedRiemannSurface X) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∀ {D : Jacobians.Divisor X}, Jacobians.Divisor.deg X D < 0 →
      ∀ {f : Jacobians.MeromorphicFunction X}, f ∈ Jacobians.linearSystem D →
        ∀ x, f.orderW x = ⊤ := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  dsimp only
  intro D hD f hf
  let : FiniteDimensional ℂ (Jacobians.Dolbeault.lSysModule D) :=
    Jacobians.LaurentTail.finiteDimensional_lSysModule D
  have hdim : Module.finrank ℂ (Jacobians.Dolbeault.lSysModule D) = 0 :=
    Jacobians.lDim_eq_zero_of_deg_neg D hD
  let : Subsingleton (Jacobians.Dolbeault.lSysModule D) :=
    Module.finrank_zero_iff.mp hdim
  have hzero :
      (Submodule.Quotient.mk (⟨f, hf⟩ : Jacobians.linearSystem D) :
        Jacobians.Dolbeault.lSysModule D) = 0 := Subsingleton.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp hzero

/-- A meromorphic function with a nonzero germ can belong only to a linear
system whose divisor has nonnegative degree. -/
theorem degree_nonneg_of_mem_linearSystem_of_nonzero_germ (R : ClosedRiemannSurface X) :
    let := R.t2Space
    let := R.compactSpace
    let := R.connectedSpace
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    ∀ {D : Jacobians.Divisor X} {f : Jacobians.MeromorphicFunction X},
      f ∈ Jacobians.linearSystem D → (∃ x, f.orderW x ≠ ⊤) →
        0 ≤ Jacobians.Divisor.deg X D := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  dsimp only
  intro D f hf hnonzero
  by_contra hnegative
  obtain ⟨x, hx⟩ := hnonzero
  exact hx (R.germ_zero_of_mem_linearSystem_of_degree_neg (lt_of_not_ge hnegative) hf x)

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface
