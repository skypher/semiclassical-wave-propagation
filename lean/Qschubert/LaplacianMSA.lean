import Qschubert.Density
import Qschubert.Friedrichs

/-!
# The self-adjoint Laplacian `-Δ_M` on `L²(M)`

Spine stage S4 (`lean/BLUEPRINT.md`, representation choice 3). For a Fuchsian `Γ`, `-Δ_M` on the
periodized test functions is the operator with graph `{(F_Γ, -(ΔF)_Γ) : F test function}`. It is
well defined (if `F_Γ = 0` then `(ΔF)_Γ` is orthogonal to every `G_Γ` by symmetry, hence `0` by
density), densely defined, symmetric and nonnegative. Its Friedrichs extension `negLapMH` is
self-adjoint and nonnegative and extends it. This is the definition of `-Δ_M` used here; its
identification with other self-adjoint realizations (essential self-adjointness on the core) is
not claimed.
-/

namespace Qschubert

open MeasureTheory Complex Filter Topology Physicslib4.Spectral.Unbounded
open scoped ComplexConjugate ContDiff MatrixGroups UpperHalfPlane

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- The graph `{(F_Γ, -(ΔF)_Γ)}`. -/
noncomputable def lapGraphM : Submodule ℂ (Lp ℂ 2 (surfMeasure Γ) × Lp ℂ 2 (surfMeasure Γ)) :=
  LinearMap.range (LinearMap.prod (perioTLin Γ) (-((perioTLin Γ).comp lapTest)))

lemma mem_lapGraphM (F : testFn) : (perioT Γ F, -perioT Γ (lapTest F)) ∈ lapGraphM Γ :=
  ⟨F, rfl⟩

/-- The graph is the graph of a function: `F_Γ = 0` forces `(ΔF)_Γ = 0`. -/
lemma lapGraphM_functional : ∀ (x : Lp ℂ 2 (surfMeasure Γ) × Lp ℂ 2 (surfMeasure Γ))
    (_hx : x ∈ lapGraphM Γ) (_hx' : x.fst = 0), x.snd = 0 := by
  rintro x ⟨F, rfl⟩ hx
  have h0 : perioT Γ F = 0 := hx
  have : perioT Γ (lapTest F) = 0 := by
    refine eq_zero_of_orth Γ _ fun G => ?_
    rw [inner_eq_zero_symm, perioT_lap_symm, h0, inner_zero_right]
  show -perioT Γ (lapTest F) = 0
  rw [this, neg_zero]

/-- `-Δ_M` on the periodized test functions. -/
noncomputable def negLapM : Lp ℂ 2 (surfMeasure Γ) →ₗ.[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  (lapGraphM Γ).toLinearPMap

lemma negLapM_domain : (negLapM Γ).domain = LinearMap.range (perioTLin Γ) := by
  rw [negLapM, Submodule.toLinearPMap_domain, lapGraphM, ← LinearMap.range_comp,
    LinearMap.fst_prod]

lemma perioT_mem_negLapM_domain (F : testFn) : perioT Γ F ∈ (negLapM Γ).domain := by
  rw [negLapM_domain]; exact ⟨F, rfl⟩

/-- On `F_Γ`, `-Δ_M` is `-(ΔF)_Γ`. -/
theorem negLapM_apply (F : testFn) (h : perioT Γ F ∈ (negLapM Γ).domain) :
    negLapM Γ ⟨perioT Γ F, h⟩ = -perioT Γ (lapTest F) := by
  have h1 := Submodule.mem_graph_toLinearPMap (lapGraphM_functional Γ) ⟨perioT Γ F, h⟩
  have h2 := mem_lapGraphM Γ F
  have h3 := (lapGraphM Γ).sub_mem h1 h2
  have h4 := lapGraphM_functional Γ _ h3 (by simp)
  simp only [Prod.snd_sub, sub_neg_eq_add] at h4
  exact eq_neg_of_add_eq_zero_left h4

lemma exists_eq_perioT (φ : (negLapM Γ).domain) : ∃ F : testFn, perioT Γ F = φ := by
  have h : (φ : Lp ℂ 2 (surfMeasure Γ)) ∈ LinearMap.range (perioTLin Γ) := by
    rw [← negLapM_domain Γ]; exact φ.2
  obtain ⟨F, hF⟩ := h
  exact ⟨F, hF⟩

lemma negLapM_apply_of_eq (φ : (negLapM Γ).domain) (F : testFn) (hF : perioT Γ F = φ) :
    negLapM Γ φ = -perioT Γ (lapTest F) := by
  have e : φ = ⟨perioT Γ F, perioT_mem_negLapM_domain Γ F⟩ := Subtype.ext hF.symm
  rw [e, negLapM_apply]

theorem negLapM_hasDenseDomain : HasDenseDomain (negLapM Γ) := by
  show Dense ((negLapM Γ).domain : Set (Lp ℂ 2 (surfMeasure Γ)))
  rw [negLapM_domain, LinearMap.coe_range]
  exact dense_range_perioT Γ

theorem negLapM_isSymmetric : IsSymmetric (negLapM Γ) := by
  intro φ ψ
  obtain ⟨F, hF⟩ := exists_eq_perioT Γ φ
  obtain ⟨G, hG⟩ := exists_eq_perioT Γ ψ
  rw [negLapM_apply_of_eq Γ φ F hF, negLapM_apply_of_eq Γ ψ G hG, ← hF, ← hG, inner_neg_right,
    inner_neg_left, perioT_lap_symm]

theorem negLapM_nonneg (φ : (negLapM Γ).domain) :
    0 ≤ (inner ℂ (φ : Lp ℂ 2 (surfMeasure Γ)) (negLapM Γ φ)).re := by
  obtain ⟨F, hF⟩ := exists_eq_perioT Γ φ
  rw [negLapM_apply_of_eq Γ φ F hF, ← hF]
  exact perioT_lap_nonneg Γ F

theorem negLapM_isPositive : IsPositive (negLapM Γ) :=
  ⟨negLapM_isSymmetric Γ, negLapM_nonneg Γ⟩

instance : Fact (IsPositive (negLapM Γ)) := ⟨negLapM_isPositive Γ⟩

/-- **`-Δ_M` on `L²(M)`**: the Friedrichs extension of `-Δ_M` on periodized test functions. -/
noncomputable def negLapMH : Lp ℂ 2 (surfMeasure Γ) →ₗ.[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  friedrichsExt (negLapM Γ) (negLapM_hasDenseDomain Γ)

theorem negLapMH_isSelfAdjoint : IsSelfAdjoint (negLapMH Γ) :=
  friedrichsExt_isSelfAdjoint _ (negLapM_hasDenseDomain Γ)

theorem negLapM_le_negLapMH : negLapM Γ ≤ negLapMH Γ :=
  le_friedrichsExt _ (negLapM_hasDenseDomain Γ)

theorem negLapMH_isPositive : IsPositive (negLapMH Γ) :=
  ⟨friedrichsExt_isSymmetric _ (negLapM_hasDenseDomain Γ),
    friedrichsExt_nonneg _ (negLapM_hasDenseDomain Γ)⟩

theorem negLapMH_hasDenseDomain : HasDenseDomain (negLapMH Γ) :=
  friedrichsExt_hasDenseDomain _ (negLapM_hasDenseDomain Γ)

/-- Every periodized test function lies in the domain of `-Δ_M`. -/
theorem perioT_mem_negLapMH_domain (F : testFn) : perioT Γ F ∈ (negLapMH Γ).domain :=
  (negLapM_le_negLapMH Γ).1 (perioT_mem_negLapM_domain Γ F)

/-- On periodized test functions, `-Δ_M F_Γ = -(ΔF)_Γ`. -/
theorem negLapMH_perioT (F : testFn) (h : perioT Γ F ∈ (negLapMH Γ).domain) :
    negLapMH Γ ⟨perioT Γ F, h⟩ = -perioT Γ (lapTest F) := by
  rw [← negLapM_apply Γ F (perioT_mem_negLapM_domain Γ F)]
  exact ((negLapM_le_negLapMH Γ).2 rfl).symm

end Qschubert
