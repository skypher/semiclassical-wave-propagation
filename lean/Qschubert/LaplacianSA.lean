import Qschubert.LaplacianOp
import Qschubert.Friedrichs

/-!
# The self-adjoint hyperbolic Laplacian

Spine stage S2 (`lean/BLUEPRINT.md`, representation choice 3): `-Δ` on `L²(ℍ, dx dy / y²)` is the
Friedrichs extension of `-Δ` on test functions. It is self-adjoint, nonnegative, and extends `-Δ`
on test functions.
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Physicslib4.Spectral.Unbounded

instance : Fact (IsPositive negLap) := ⟨negLap_isPositive⟩

/-- `-Δ` on `L²(ℍ)`: the Friedrichs extension of `-Δ` on test functions. -/
noncomputable def negLapH : Lp ℂ 2 (volume : Measure ℍ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  friedrichsExt negLap negLap_hasDenseDomain

theorem negLapH_isSelfAdjoint : IsSelfAdjoint negLapH :=
  friedrichsExt_isSelfAdjoint negLap negLap_hasDenseDomain

theorem negLap_le_negLapH : negLap ≤ negLapH :=
  le_friedrichsExt negLap negLap_hasDenseDomain

theorem negLapH_isPositive : IsPositive negLapH :=
  ⟨friedrichsExt_isSymmetric negLap negLap_hasDenseDomain,
    friedrichsExt_nonneg negLap negLap_hasDenseDomain⟩

theorem negLapH_hasDenseDomain : HasDenseDomain negLapH :=
  friedrichsExt_hasDenseDomain negLap negLap_hasDenseDomain

/-- Every test function lies in the domain of `negLapH`. -/
theorem toL2_mem_negLapH_domain (F : testFn) : toL2 F ∈ negLapH.domain :=
  negLap_le_negLapH.1 (toL2Equiv F).2

/-- On test functions, `negLapH` is `-Δ`. -/
theorem negLapH_toL2 (F : testFn) (h : toL2 F ∈ negLapH.domain) :
    negLapH ⟨toL2 F, h⟩ = -toL2 (lapTest F) := by
  rw [← negLap_toL2Equiv F]
  exact (negLap_le_negLapH.2 rfl).symm

end Qschubert
