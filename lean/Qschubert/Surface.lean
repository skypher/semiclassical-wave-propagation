import Qschubert.FundDomain
import Qschubert.LaplacianL2
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The quotient `M = Γ\ℍ` and its measure

Spine stage S3 (`lean/BLUEPRINT.md`, representation choice 2). For a subgroup `Γ ≤ PGL(2, ℝ)`,
`M = Γ\ℍ` is the orbit space of the action on `ℍ`, with the quotient σ-algebra. Its measure is the
pushforward of `dx dy / y²` restricted to a fundamental domain; it does not depend on the
fundamental domain (`surfMeasure_eq`). Fuchsian groups are the subgroups acting properly
discontinuously (for subgroups of `PSL(2, ℝ)`, equivalent to discreteness; Katok, Fuchsian
groups, Theorem 2.2.6). They are countable and have a fundamental domain
(`Qschubert/FundDomain.lean`), so for them the measure on `M` is not zero (`surfMeasure_ne_zero`).
Unfolding: `∫_ℍ f dν = ∫_M Σ_γ f(γ ·) dμ` for measurable `f ≥ 0` (`lintegral_eq_lintegral_automorphize`).
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Metric
open scoped MatrixGroups ENNReal

variable (Γ : Subgroup PGL(2, ℝ))

/-- `M = Γ\ℍ`. -/
abbrev Surf : Type := Quotient (MulAction.orbitRel Γ ℍ)

/-- The projection `ℍ → Γ\ℍ`. -/
noncomputable def surfMk : ℍ → Surf Γ := Quotient.mk _

lemma measurable_surfMk : Measurable (surfMk Γ) := measurable_quotient_mk''

lemma surfMk_smul (γ : Γ) (z : ℍ) : surfMk Γ (γ • z) = surfMk Γ z :=
  Quotient.sound ⟨γ, rfl⟩

open Classical in
/-- The measure on `M`: `dx dy / y²` restricted to a fundamental domain, pushed forward; `0` if
`Γ` has no fundamental domain. -/
noncomputable def surfMeasure : Measure (Surf Γ) :=
  if h : HasFundamentalDomain Γ ℍ volume then
    (volume.restrict h.ExistsIsFundamentalDomain.choose).map (surfMk Γ)
  else 0

/-- The measure on `M` is the pushforward from any fundamental domain. -/
theorem surfMeasure_eq [Countable Γ] {F : Set ℍ} (hF : IsFundamentalDomain Γ F volume) :
    surfMeasure Γ = (volume.restrict F).map (surfMk Γ) := by
  have h : HasFundamentalDomain Γ ℍ volume := ⟨⟨F, hF⟩⟩
  rw [surfMeasure, dite_eq_left h]
  exact h.ExistsIsFundamentalDomain.choose_spec.quotientMeasure_eq _ hF

/-- For a Fuchsian group the measure on `M` is not zero (nonvacuity check): every orbit meets
the fundamental domain `fdSet Γ`, so `μ(M) = ν(fdSet Γ) = 0` would force `ν(ℍ) = 0`. -/
theorem surfMeasure_ne_zero [ProperlyDiscontinuousSMul Γ ℍ] : surfMeasure Γ ≠ 0 := by
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  rw [surfMeasure_eq Γ hF]
  intro h
  have h' := congrArg (fun μ : Measure (Surf Γ) => μ Set.univ) h
  simp only [Measure.map_apply (measurable_surfMk Γ) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.coe_zero,
    Pi.zero_apply] at h'
  have h0 : volume (Set.univ : Set ℍ) = 0 :=
    hF.measure_zero_of_invariant _ (fun g => Set.smul_set_univ) (by simpa using h')
  exact (isOpen_univ.measure_pos (volume : Measure ℍ) Set.univ_nonempty).ne' h0

/-- Unfolding: `∫_ℍ f dν = ∫_M (Σ_γ f(γ ·)) dμ` for measurable `f ≥ 0`. -/
theorem lintegral_eq_lintegral_automorphize [Countable Γ] {F : Set ℍ}
    (hF : IsFundamentalDomain Γ F volume) {f : ℍ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z = ∫⁻ x, MulAction.automorphize f x ∂surfMeasure Γ := by
  have hfγ : ∀ γ : Γ, Measurable fun z : ℍ => f (γ • z) := fun γ => hf.comp (measurable_const_smul γ)
  have hm : Measurable (MulAction.automorphize f : Surf Γ → ℝ≥0∞) :=
    measurable_from_quotient.2 (Measurable.ennreal_tsum hfγ)
  rw [surfMeasure_eq Γ hF, lintegral_map hm (measurable_surfMk Γ),
    hF.lintegral_eq_tsum'' f]
  show _ = ∫⁻ z in F, ∑' γ : Γ, f (γ • z)
  rw [lintegral_tsum fun γ => (hfγ γ).aemeasurable]

end Qschubert
