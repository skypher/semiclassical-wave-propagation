import Qschubert.Surface

/-!
# Periodization into `L²(M)`

Spine stage S3 (`lean/BLUEPRINT.md`). For `u : ℍ → ℂ`, `u_Γ = Σ_γ u ∘ γ` on `M = Γ\ℍ`
(Schubert writes `Σ_γ u ∘ γ⁻¹`, the same sum reindexed), as Mathlib's `MulAction.automorphize`.
For a Fuchsian group and `u` continuous with compact support: the translates have locally finite
supports, `u_Γ` is continuous, bounded by `N_K sup|u|` where `N_K` counts the `γ` with `γK ∩ K ≠ ∅`,
and lies in `L²(M)`. Unfolding for integrable `h`: `∫_ℍ h = ∫_M h_Γ`.
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Metric
open scoped MatrixGroups ENNReal Pointwise

variable (Γ : Subgroup PGL(2, ℝ))

/-- `u_Γ = Σ_γ u ∘ γ` on `M`. -/
noncomputable def perio (u : ℍ → ℂ) : Surf Γ → ℂ := MulAction.automorphize u

lemma perio_mk (u : ℍ → ℂ) (z : ℍ) : perio Γ u (surfMk Γ z) = ∑' γ : Γ, u (γ • z) := rfl

/-- Unfolding for integrable `h`: `∫_ℍ h dν = ∫_M h_Γ dμ`. -/
theorem integral_eq_integral_automorphize [Countable Γ] {F : Set ℍ}
    (hF : IsFundamentalDomain Γ F volume) {h : ℍ → ℂ} (hh : Integrable h)
    (hm : AEStronglyMeasurable (MulAction.automorphize h : Surf Γ → ℂ) (surfMeasure Γ)) :
    ∫ z, h z = ∫ x, MulAction.automorphize h x ∂surfMeasure Γ := by
  have hγ : ∀ γ : Γ, AEStronglyMeasurable (fun z => h (γ • z)) (volume.restrict F) := fun γ =>
    (hh.1.comp_quasiMeasurePreserving
      (measurePreserving_smul γ volume).quasiMeasurePreserving).restrict
  have hl := hF.lintegral_eq_tsum'' (fun z => ‖h z‖ₑ)
  rw [hF.integral_eq_tsum'' h hh, ← integral_tsum hγ (by rw [← hl]; exact hh.2.ne)]
  rw [surfMeasure_eq Γ hF] at hm ⊢
  rw [integral_map (measurable_surfMk Γ).aemeasurable hm]
  rfl

variable [ProperlyDiscontinuousSMul Γ ℍ]

/-- For compactly supported `u`, the supports of the translates `u ∘ γ` are locally finite. -/
lemma locallyFinite_support_smul {u : ℍ → ℂ} (hu : HasCompactSupport u) :
    LocallyFinite fun γ : Γ => Function.support fun z => u (γ • z) := by
  intro x
  refine ⟨closedBall x 1, closedBall_mem_nhds x one_pos, ?_⟩
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ)
    (isCompact_closedBall x 1) hu).subset ?_
  rintro γ ⟨z, hz1, hz2⟩
  exact ⟨γ • z, ⟨z, hz2, rfl⟩, subset_tsupport _ hz1⟩

/-- The lift of `u_Γ` to `ℍ` is continuous for continuous compactly supported `u`. -/
theorem continuous_perio_mk {u : ℍ → ℂ} (hc : Continuous u) (hu : HasCompactSupport u) :
    Continuous fun z => perio Γ u (surfMk Γ z) := by
  have hlf := locallyFinite_support_smul Γ hu
  have e : (fun z => perio Γ u (surfMk Γ z)) = fun z => ∑ᶠ γ : Γ, u (γ • z) := by
    funext z
    rw [perio_mk]
    exact tsum_eq_finsum (hlf.point_finite z)
  rw [e]
  exact continuous_finsum (fun γ => hc.comp (continuous_const_smul γ)) hlf

theorem measurable_perio {u : ℍ → ℂ} (hc : Continuous u) (hu : HasCompactSupport u) :
    Measurable (perio Γ u) :=
  measurable_from_quotient.2 (continuous_perio_mk Γ hc hu).measurable

/-- `N_K`: the number of `γ` with `γK ∩ K ≠ ∅` (finite for compact `K`). -/
noncomputable def orbitCount (K : Set ℍ) : ℕ :=
  Set.ncard {γ : Γ | ((γ • ·) '' K ∩ K).Nonempty}

/-- At most `N_K` translates of a point lie in `K`. -/
lemma ncard_smul_mem_le {K : Set ℍ} (hK : IsCompact K) (x : ℍ) :
    Set.ncard {γ : Γ | γ • x ∈ K} ≤ orbitCount Γ K := by
  have hT := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) hK hK
  rcases Set.eq_empty_or_nonempty {γ : Γ | γ • x ∈ K} with h | ⟨γ₀, hγ₀⟩
  · rw [h, Set.ncard_empty]; exact Nat.zero_le _
  · have hsub : {γ : Γ | γ • x ∈ K} ⊆ (fun δ => δ * γ₀) '' {γ : Γ | ((γ • ·) '' K ∩ K).Nonempty} := by
      intro γ hγ
      refine ⟨γ * γ₀⁻¹, ⟨γ • x, ⟨γ₀ • x, hγ₀, ?_⟩, hγ⟩, by simp⟩
      simp [smul_smul]
    calc Set.ncard {γ : Γ | γ • x ∈ K}
        ≤ Set.ncard ((fun δ => δ * γ₀) '' {γ : Γ | ((γ • ·) '' K ∩ K).Nonempty}) :=
          Set.ncard_le_ncard hsub (hT.image _)
      _ ≤ orbitCount Γ K := Set.ncard_image_le hT

/-- `|u_Γ| ≤ N_K sup|u|` with `K = tsupport u`. -/
lemma norm_perio_le {u : ℍ → ℂ} (hu : HasCompactSupport u) {C : ℝ} (hC : ∀ z, ‖u z‖ ≤ C)
    (x : Surf Γ) : ‖perio Γ u x‖ ≤ orbitCount Γ (tsupport u) * C := by
  induction x using Quotient.inductionOn with | _ z
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC z)
  have hfin := (locallyFinite_support_smul Γ hu).point_finite z
  have e : perio Γ u (Quotient.mk _ z) = ∑ γ ∈ hfin.toFinset, u (γ • z) :=
    tsum_eq_sum (fun γ hγ => by simpa using hγ)
  rw [e]
  have hcard : hfin.toFinset.card ≤ orbitCount Γ (tsupport u) := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (ncard_smul_mem_le Γ hu z)
    · intro γ hγ
      exact subset_tsupport _ hγ
    · exact (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ)
        isCompact_singleton hu).subset fun γ hγ => ⟨γ • z, ⟨z, rfl, rfl⟩, hγ⟩
  calc ‖∑ γ ∈ hfin.toFinset, u (γ • z)‖ ≤ ∑ γ ∈ hfin.toFinset, ‖u (γ • z)‖ := norm_sum_le _ _
    _ ≤ hfin.toFinset.card * C := by
        have := Finset.sum_le_card_nsmul hfin.toFinset (fun γ => ‖u (γ • z)‖) C (fun γ _ => hC _)
        simpa using this
    _ ≤ orbitCount Γ (tsupport u) * C := by
        gcongr

/-- For continuous compactly supported `u`, `u_Γ ∈ L²(M)`. -/
theorem memLp_perio {u : ℍ → ℂ} (hc : Continuous u) (hu : HasCompactSupport u) :
    MemLp (perio Γ u) 2 (surfMeasure Γ) := by
  have := countable_of_properlyDiscontinuous Γ
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hu
  have hF := isFundamentalDomain_fdSet Γ
  have hae := (measurable_perio Γ hc hu).aestronglyMeasurable (μ := surfMeasure Γ)
  rw [memLp_iff]
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hae]
  set B := ENNReal.ofReal (orbitCount Γ (tsupport u) * C)
  have hpt : ∀ x : Surf Γ, ‖perio Γ u x‖ₑ ^ (2 : ℝ≥0∞).toReal
      ≤ B * MulAction.automorphize (fun z => ‖u z‖ₑ) x := by
    intro x
    have h1 : ‖perio Γ u x‖ₑ ≤ B := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (norm_perio_le Γ hu hC x)
    have h2 : ‖perio Γ u x‖ₑ ≤ MulAction.automorphize (fun z => ‖u z‖ₑ) x := by
      induction x using Quotient.inductionOn with | _ z
      exact enorm_tsum_le_tsum_enorm
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_two, sq]
    exact mul_le_mul' h1 h2
  have hint := (hc.integrable_of_hasCompactSupport hu (μ := (volume : Measure ℍ))).2
  calc ∫⁻ x, ‖perio Γ u x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂surfMeasure Γ
      ≤ ∫⁻ x, B * MulAction.automorphize (fun z => ‖u z‖ₑ) x ∂surfMeasure Γ := lintegral_mono hpt
    _ = B * ∫⁻ x, MulAction.automorphize (fun z => ‖u z‖ₑ) x ∂surfMeasure Γ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = B * ∫⁻ z, ‖u z‖ₑ := by
        rw [← lintegral_eq_lintegral_automorphize Γ hF hc.enorm.measurable]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

/-- `u_Γ` as an element of `L²(M)`. -/
noncomputable def perioL2 {u : ℍ → ℂ} (hc : Continuous u) (hu : HasCompactSupport u) :
    Lp ℂ 2 (surfMeasure Γ) :=
  (memLp_perio Γ hc hu).toLp _

lemma perioL2_ae (u : ℍ → ℂ) (hc : Continuous u) (hu : HasCompactSupport u) :
    ⇑(perioL2 Γ hc hu) =ᵐ[surfMeasure Γ] perio Γ u :=
  (memLp_perio Γ hc hu).coeFn_toLp

/-- `⟪v_Γ, u_Γ⟫_{L²(M)} = ∫_ℍ conj(v_Γ) u dν` for continuous compactly supported `u, v`
(Mathlib's inner product is conjugate-linear in the first slot). -/
theorem inner_perioL2 {u v : ℍ → ℂ} (hcu : Continuous u) (hu : HasCompactSupport u)
    (hcv : Continuous v) (hv : HasCompactSupport v) :
    inner ℂ (perioL2 Γ hcv hv) (perioL2 Γ hcu hu)
      = ∫ z, (starRingEnd ℂ) (perio Γ v (surfMk Γ z)) * u z := by
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  have key : MulAction.automorphize (fun z => (starRingEnd ℂ) (perio Γ v (surfMk Γ z)) * u z)
      = fun x => (starRingEnd ℂ) (perio Γ v x) * perio Γ u x :=
    MulAction.automorphize_smul_left (α := Γ) u (fun x => (starRingEnd ℂ) (perio Γ v x))
  have hint : Integrable (fun z => (starRingEnd ℂ) (perio Γ v (surfMk Γ z)) * u z) :=
    ((Complex.continuous_conj.comp (continuous_perio_mk Γ hcv hv)).mul hcu).integrable_of_hasCompactSupport
      (hu.mul_left)
  have hm : AEStronglyMeasurable (MulAction.automorphize
      (fun z => (starRingEnd ℂ) (perio Γ v (surfMk Γ z)) * u z) : Surf Γ → ℂ) (surfMeasure Γ) := by
    rw [key]
    exact ((Complex.continuous_conj.measurable.comp (measurable_perio Γ hcv hv)).mul
      (measurable_perio Γ hcu hu)).aestronglyMeasurable
  rw [integral_eq_integral_automorphize Γ hF hint hm, key, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [perioL2_ae Γ u hcu hu, perioL2_ae Γ v hcv hv] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]

end Qschubert
