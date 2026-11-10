import Qschubert.Density

/-!
# The measure on `M = Γ\ℍ` has full support (CL-SUPP)

For a Fuchsian `Γ`, `surfMeasure Γ` charges every nonempty open subset of `M` (quotient topology):
its preimage in `ℍ` is a nonempty open invariant set, of positive volume; if its intersection with a
fundamental domain were null, the invariant set would be null. Consequence: continuous functions on
`M` that agree a.e. agree everywhere (`eq_of_ae_eq_of_continuous`), so a continuous representative of
an `L²(M)` class is unique.
-/

namespace Qschubert

open MeasureTheory
open scoped MatrixGroups Pointwise UpperHalfPlane

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma continuous_surfMk : Continuous (surfMk Γ) := continuous_quotient_mk'

instance : (surfMeasure Γ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  have hpre : IsOpen (surfMk Γ ⁻¹' U) := hU.preimage (continuous_surfMk Γ)
  have hne' : (surfMk Γ ⁻¹' U).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    induction x using Quotient.inductionOn with | _ z
    exact ⟨z, hx⟩
  have hmeas : MeasurableSet U := hpre.measurableSet
  rw [surfMeasure_eq Γ hF, Measure.map_apply (measurable_surfMk Γ) hmeas,
    Measure.restrict_apply hpre.measurableSet]
  intro h0
  have hinv : ∀ g : Γ, g • (surfMk Γ ⁻¹' U) = surfMk Γ ⁻¹' U := by
    intro g; ext z
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage, surfMk_smul]
  have := hF.measure_zero_of_invariant _ hinv h0
  exact (hpre.measure_pos (volume : Measure ℍ) hne').ne' this

theorem surfMeasure_isOpenPosMeasure : (surfMeasure Γ).IsOpenPosMeasure := inferInstance

/-- Continuous functions on `M` that agree `μ`-a.e. agree everywhere. -/
theorem eq_of_ae_eq_of_continuous {f g : Surf Γ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[surfMeasure Γ] g) : f = g :=
  (Continuous.ae_eq_iff_eq (surfMeasure Γ) hf hg).1 h

end Qschubert
