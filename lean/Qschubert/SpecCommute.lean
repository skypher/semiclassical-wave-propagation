import Qschubert.KLDensity
import Qschubert.GLInvariance

/-!
# Functions of the Laplacian commute with the isometries of `ℍ`

Stage X of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For `φ` continuous and vanishing at infinity and
`g ∈ GL(2, ℝ)`: `φ(-Δ) U_g = U_g φ(-Δ)` (`fc_glU`), where `U_g f = f ∘ (g •)`.

Proof: `klU ∘ U_g` intertwines `-Δ` with multiplication by `ν² + 1/4` (`negLapH_glU`, `klU_negLapH`), so by the transfer
theorem `isGood_of_tendsto_cocompact` both `klU (U_g φ(-Δ) η)` and `klU (φ(-Δ) U_g η)` are `φ(ν² + 1/4) · klU (U_g η)`;
and `klU` is injective.
-/

namespace Qschubert

open MeasureTheory Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped UpperHalfPlane

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- **`φ(-Δ)` commutes with the isometries of `ℍ`**, for `φ` continuous and vanishing at infinity. -/
theorem fc_glU {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : Tendsto φ (cocompact ℝ) (𝓝 0)) (g : GL (Fin 2) ℝ) (η : L2H) :
    (spectralMeasure negLapH_isSelfAdjoint).integral φ (glU g η)
      = glU g ((spectralMeasure negLapH_isSelfAdjoint).integral φ η) := by
  set V : L2H →L[ℂ] Lp ℂ 2 muU := klU.comp (glU g).toLinearIsometry.toContinuousLinearMap with hV
  have hVa : ∀ x : L2H, V x = klU (glU g x) := fun x => rfl
  have hV' : ∀ x : negLapH.domain, ((V (negLapH x) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => (((p.2 ^ 2 + 1 / 4 : ℝ)) : ℂ) * (V (x : L2H) : ℝ × ℝ → ℂ) p := by
    intro x
    obtain ⟨hd, he⟩ := negLapH_glU g x
    rw [hVa, hVa, ← he]
    filter_upwards [klU_negLapH ⟨glU g x, hd⟩] with p hp
    rw [hp]
    push_cast
    ring
  have h1 := isGood_of_tendsto_cocompact (hA := negLapH_isSelfAdjoint) hV' (by fun_prop) hφc hφ0 η
  have h2 := klU_functionalCalculus hφc hφ0 (glU g η)
  have h3 : klU (glU g ((spectralMeasure negLapH_isSelfAdjoint).integral φ η))
      = klU ((spectralMeasure negLapH_isSelfAdjoint).integral φ (glU g η)) := by
    refine Lp.ext ?_
    filter_upwards [h1, h2] with p e1 e2
    rw [hVa, hVa] at e1
    rw [e1, e2]
  have h4 : klUi (glU g ((spectralMeasure negLapH_isSelfAdjoint).integral φ η))
      = klUi ((spectralMeasure negLapH_isSelfAdjoint).integral φ (glU g η)) := h3
  exact (klUi.injective h4).symm

end Qschubert
