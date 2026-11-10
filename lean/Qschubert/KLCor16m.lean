import Qschubert.KLCor16c
import Qschubert.PGLAction

/-!
# The Sobolev bound on a Fuchsian quotient, with the multiplicity factor (Lemma `pc:g43`)

`sobolev_M_mult`: for every `Γ` acting properly discontinuously and every `u ∈ Dom(-Δ_M)`, `u` has a continuous representative `f` with

`|f(x)| ≤ K m(x)^{1/2} (‖u‖ + ‖Δ_M u‖)`,   `m(x) = #{γ : d(z, γ z) < 2}` at a lift `z` of `x`,

with an absolute constant `K`. The proof is the one of `sobolev_M`, without the injectivity radius: a cut-off supported in the hyperbolic
unit ball around a lift meets every orbit at most `m` times (`encard_ball_le_orbitMult`), so the cut costs the factor `m^{1/2}` (`CutB`).
As in `sobolev_M`, one Laplacian is used, where the manuscript uses `Δ²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- The multiplicity is finite. -/
lemma orbitMult_ne_top (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (z : ℍ) : orbitMult Γ z ≠ ⊤ := by
  unfold orbitMult
  rw [Set.encard_ne_top_iff]
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (T := ℍ) (isCompact_singleton (x := z))
    (isCompact_closedBall z 2)
  refine hfin.subset fun γ hγ => ?_
  show ((fun x => γ • x) '' {z} ∩ Metric.closedBall z 2).Nonempty
  rw [Set.image_singleton]
  refine ⟨γ • z, rfl, ?_⟩
  rw [Metric.mem_closedBall, dist_comm]
  exact le_of_lt hγ

/-- The multiplicity is invariant under conjugation. -/
lemma orbitMult_conj (p : PGL(2, ℝ)) (Γ : Subgroup PGL(2, ℝ)) (z : ℍ) : orbitMult (conjS p Γ) (p • z) = orbitMult Γ z := by
  unfold orbitMult
  have e : {γ' : conjS p Γ | dist (p • z) (γ' • p • z) < 2} = (conjE p Γ) '' {γ : Γ | dist z (γ • z) < 2} := by
    ext γ'
    constructor
    · intro h
      obtain ⟨γ, rfl⟩ := (conjE p Γ).surjective γ'
      refine ⟨γ, ?_, rfl⟩
      have h' : dist (p • z) (conjE p Γ γ • p • z) < 2 := h
      rwa [conjE_smul, dist_smul] at h'
    · rintro ⟨γ, h, rfl⟩
      show dist (p • z) (conjE p Γ γ • p • z) < 2
      rw [conjE_smul, dist_smul]
      exact h
  rw [e, (conjE p Γ).injective.injOn.encard_image]

/-- `m(z)^{1/2}` as a real number. -/
noncomputable def sqrtMult (Γ : Subgroup PGL(2, ℝ)) (z : ℍ) : ℝ := Real.sqrt ((orbitMult Γ z).toNat : ℝ)

lemma sqrtMult_nonneg (Γ : Subgroup PGL(2, ℝ)) (z : ℍ) : 0 ≤ sqrtMult Γ z := Real.sqrt_nonneg _

lemma orbitMult_cast (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (z : ℍ) :
    (orbitMult Γ z : ℝ≥0∞) = ((orbitMult Γ z).toNat : ℝ≥0∞) := by
  have h := ENat.coe_toNat (orbitMult_ne_top Γ z)
  conv_lhs => rw [← h]
  exact ENat.toENNReal_coe _

lemma orbitMult_le_sqrtMult (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (z : ℍ) :
    (orbitMult Γ z : ℝ≥0∞) ≤ ENNReal.ofReal (sqrtMult Γ z ^ 2) := by
  unfold sqrtMult
  rw [Real.sq_sqrt (Nat.cast_nonneg _), ENNReal.ofReal_natCast, orbitMult_cast]

lemma ofReal_sqrtMult (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (z : ℍ) :
    ENNReal.ofReal (sqrtMult Γ z) = (orbitMult Γ z : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
  unfold sqrtMult
  rw [orbitMult_cast, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _) (by norm_num), ENNReal.ofReal_natCast]

section cut

variable {Γ : Subgroup PGL(2, ℝ)}

/-- **A cut-off supported in the hyperbolic unit ball at `i` costs `m(i)^{1/2}`.** -/
lemma cutB_of_ball {χ : testFn} (hsupp : ∀ w : ℍ, (χ : ℂ → ℂ) w ≠ 0 → dist w UpperHalfPlane.I < 1) {μ : ℝ} (hμ : 0 ≤ μ)
    (hm : (orbitMult Γ UpperHalfPlane.I : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2)) : CutB Γ χ μ := by
  classical
  refine ⟨hμ, fun z => ?_⟩
  have hbd : ∀ w : ℂ, ‖(χ : ℂ → ℂ) w‖ₑ ^ 2 ≤ ENNReal.ofReal (supT χ ^ 2) := fun w => by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_le_supT χ w) 2)
  have h1 : ∀ γ : Γ, ‖(χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ)‖ₑ ^ 2
      ≤ {γ : Γ | dist (γ • z) UpperHalfPlane.I < 1}.indicator (fun _ => ENNReal.ofReal (supT χ ^ 2)) γ := fun γ => by
    by_cases h : (χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ) = 0
    · rw [h]; simp
    · rw [Set.indicator_of_mem (show γ ∈ {γ : Γ | dist (γ • z) UpperHalfPlane.I < 1} from hsupp _ h)]
      exact hbd _
  calc ∑' γ : Γ, ‖(χ : ℂ → ℂ) ((γ • z : ℍ) : ℂ)‖ₑ ^ 2
      ≤ ∑' γ : Γ, {γ : Γ | dist (γ • z) UpperHalfPlane.I < 1}.indicator (fun _ => ENNReal.ofReal (supT χ ^ 2)) γ := ENNReal.tsum_le_tsum h1
    _ = ({γ : Γ | dist (γ • z) UpperHalfPlane.I < 1}.encard : ℝ≥0∞) * ENNReal.ofReal (supT χ ^ 2) := by
        rw [← tsum_subtype, ENNReal.tsum_set_const]
    _ ≤ (orbitMult Γ UpperHalfPlane.I : ℝ≥0∞) * ENNReal.ofReal (supT χ ^ 2) := by
        gcongr
        exact encard_ball_le_orbitMult UpperHalfPlane.I z
    _ ≤ ENNReal.ofReal (μ ^ 2) * ENNReal.ofReal (supT χ ^ 2) := by gcongr
    _ = ENNReal.ofReal ((supT χ * μ) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end cut

/-- **The chart at `i` with the multiplicity factor**, uniformly over all groups. -/
theorem chart_rep_mult : ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] {μ : ℝ}, 0 ≤ μ → (orbitMult Γ UpperHalfPlane.I : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2) →
      ∀ u : (negLapMH Γ).domain,
      ∃ f : ℂ → ℂ, Continuous f ∧ (∀ᵐ z : ℍ ∂(volume : Measure ℍ), dist (z : ℂ) Complex.I < r → liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) z = f z) ∧
        ∀ ζ, ‖f ζ‖ ≤ K * (μ * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖)) := by
  have h0 : (0 : ℝ) < 1 := one_pos
  have hρ := rho_pos h0
  have hρ8 : rho 1 ≤ 1 / 8 := rho_le
  have r0 : 0 < rho 1 / 2 := by linarith
  have r1 : 0 < rho 1 / 4 := by linarith
  have r2 : 0 < rho 1 / 8 := by linarith
  have s0 : 2 * (rho 1 / 2) < 1 := by linarith
  have s1 : 2 * (rho 1 / 4) < 1 := by linarith
  have s2 : 2 * (rho 1 / 8) < 1 := by linarith
  set χ₀ := chiR (rho 1 / 2) r0 s0
  set χ₁ := chiR (rho 1 / 4) r1 s1
  set χ₂ := chiR (rho 1 / 8) r2 s2
  have hK : 0 ≤ Kloc * (supT χ₂ + Kdom χ₂ χ₁ χ₀) :=
    mul_nonneg Kloc_nonneg (add_nonneg (supT_nonneg _) (Kdom_nonneg _ _ _))
  refine ⟨Kloc * (supT χ₂ + Kdom χ₂ χ₁ χ₀), rho 1 / 8, hK, r2, ?_⟩
  intro Γ _ μ hμ hm u
  have hsupp : ∀ {r : ℝ} {hr : 0 < r} {h1 : 2 * r < 1}, 2 * r ≤ rho 1 → ∀ w : ℍ, (chiR r hr h1 : ℂ → ℂ) w ≠ 0 → dist w UpperHalfPlane.I < 1 :=
    fun h w hw => dist_lt_of_near h0 ((chiR_ne hw).le.trans h)
  have hi2 : CutB Γ χ₂ μ := cutB_of_ball (hsupp (by linarith)) hμ hm
  have hi1 : CutB Γ χ₁ μ := cutB_of_ball (hsupp (by linarith)) hμ hm
  have hi0 : CutB Γ χ₀ μ := cutB_of_ball (hsupp (by linarith)) hμ hm
  have h21 : OneOn χ₁ χ₂ := oneOn_chiR (by linarith)
  have h10 : OneOn χ₀ χ₁ := oneOn_chiR (by linarith)
  obtain ⟨hv, hb⟩ := cut_dom (isRealT_chiR (hr := r2) (h1 := s2)) (isRealT_chiR (hr := r1) (h1 := s1)) (isRealT_chiR (hr := r0) (h1 := s0))
    hi2 hi1 hi0 h21 h10 u
  obtain ⟨f, hfc, hfa, hfb⟩ := local_rep ⟨cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ)), hv⟩
  refine ⟨f, hfc, ?_, fun ζ => (hfb ζ).trans ?_⟩
  · filter_upwards [hfa, cutV_ae hi2 (u : Lp ℂ 2 (surfMeasure Γ))] with z h1 h2 hz
    have hz' : dist (z : ℂ) Complex.I < 1 / 4 := by linarith
    have e := h1 hz'
    have e' : (cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ)) : L2H') z = f z := e
    rw [h2] at e'
    rwa [show (χ₂ : ℂ → ℂ) z = 1 from chiR_one hz.le, one_mul] at e'
  · have hn := norm_cutV_le hi2 (u : Lp ℂ 2 (surfMeasure Γ))
    have hU := norm_nonneg (u : Lp ℂ 2 (surfMeasure Γ))
    have hW := norm_nonneg (negLapMH Γ u)
    have hS := supT_nonneg χ₂
    have hsum : ‖cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapH ⟨cutV hi2 (u : Lp ℂ 2 (surfMeasure Γ)), hv⟩‖
        ≤ (supT χ₂ + Kdom χ₂ χ₁ χ₀) * (μ * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖)) := by
      nlinarith [mul_nonneg (mul_nonneg hS hμ) hW]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hsum Kloc_nonneg

/-- A patch at every point, with the multiplicity at that point. -/
theorem patch_rep_mult {K r : ℝ} (hr : 0 < r)
    (hrep : ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] {μ : ℝ}, 0 ≤ μ →
      (orbitMult Γ UpperHalfPlane.I : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2) → ∀ u : (negLapMH Γ).domain,
      ∃ f : ℂ → ℂ, Continuous f ∧ (∀ᵐ z : ℍ ∂(volume : Measure ℍ), dist (z : ℂ) Complex.I < r → liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) z = f z) ∧
        ∀ ζ, ‖f ζ‖ ≤ K * (μ * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖)))
    (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (u : (negLapMH Γ).domain) (z₀ : ℍ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hm : (orbitMult Γ z₀ : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2)) :
    ∃ F : ℍ → ℂ, Continuous F ∧ ∃ V : Set ℍ, IsOpen V ∧ z₀ ∈ V ∧ (∀ᵐ w ∂(volume : Measure ℍ), w ∈ V → liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) w = F w) ∧
      ∀ w, ‖F w‖ ≤ K * (μ * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖)) := by
  obtain ⟨p, hp⟩ := exists_pgl_to_I z₀
  set v : Lp ℂ 2 (surfMeasure (conjS p Γ)) := (conjU p Γ).symm (u : Lp ℂ 2 (surfMeasure Γ)) with hv
  obtain ⟨hvd, hAv⟩ : ∃ h : v ∈ (negLapMH (conjS p Γ)).domain,
      negLapMH (conjS p Γ) ⟨v, h⟩ = (conjU p Γ).symm (negLapMH Γ u) :=
    friedrichsExt_U2 (negLapM Γ) (negLapM (conjS p Γ)) (negLapM_hasDenseDomain Γ) (negLapM_hasDenseDomain _)
      (intertwines_conj_symm p Γ) (intertwines_conj p Γ) u
  have hm' : (orbitMult (conjS p Γ) UpperHalfPlane.I : ℝ≥0∞) ≤ ENNReal.ofReal (μ ^ 2) := by
    rw [← hp, orbitMult_conj]
    exact hm
  obtain ⟨f, hfc, hfa, hfb⟩ := hrep (conjS p Γ) hμ hm' ⟨v, hvd⟩
  have hsmul : Continuous fun w : ℍ => ((p • w : ℍ) : ℂ) := UpperHalfPlane.continuous_coe.comp (continuous_const_smul p)
  refine ⟨fun w => f ((p • w : ℍ) : ℂ), hfc.comp hsmul, {w | dist ((p • w : ℍ) : ℂ) Complex.I < r},
    isOpen_lt (hsmul.dist continuous_const) continuous_const, ?_, ?_, fun w => ?_⟩
  · show dist ((p • z₀ : ℍ) : ℂ) Complex.I < r
    rw [hp]
    show dist Complex.I Complex.I < r
    rw [dist_self]; exact hr
  · have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae hfa
    have hU : conjU p Γ v = (u : Lp ℂ 2 (surfMeasure Γ)) := (conjU p Γ).apply_symm_apply _
    have h2 := ae_comp_surfMk Γ (conjU_ae p Γ v)
    filter_upwards [h1, h2] with w e1 e2 hw
    have e3 := e1 hw
    rw [hU] at e2
    have e4 : liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) w = liftM (conjS p Γ) v (p • w) := e2
    rw [e4]
    exact e3
  · refine (hfb _).trans (le_of_eq ?_)
    congr 3
    · exact LinearIsometryEquiv.norm_map _ _
    · rw [hAv]; exact LinearIsometryEquiv.norm_map _ _

/-- **Gluing** local continuous representatives, with a bound at the centre of each patch. -/
theorem glue_rep_pt {u' : ℍ → ℂ} {B : ℍ → ℝ}
    (hp : ∀ z₀ : ℍ, ∃ F : ℍ → ℂ, Continuous F ∧ ∃ V : Set ℍ, IsOpen V ∧ z₀ ∈ V ∧ (∀ᵐ w ∂(volume : Measure ℍ), w ∈ V → u' w = F w) ∧ ‖F z₀‖ ≤ B z₀) :
    ∃ F : ℍ → ℂ, Continuous F ∧ F =ᵐ[volume] u' ∧ ∀ z, ‖F z‖ ≤ B z := by
  choose Fz hFc V hVo hVm hFa hFb using hp
  have hag : ∀ a b : ℍ, ∀ w ∈ V a ∩ V b, Fz a w = Fz b w := by
    intro a b
    have hO : IsOpen (V a ∩ V b) := (hVo a).inter (hVo b)
    have hae : Fz a =ᵐ[(volume : Measure ℍ).restrict (V a ∩ V b)] Fz b := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hO.measurableSet]
      filter_upwards [hFa a, hFa b] with w h1 h2 hw
      rw [← h1 hw.1, ← h2 hw.2]
    exact Measure.eqOn_open_of_ae_eq hae hO (hFc a).continuousOn (hFc b).continuousOn
  set F : ℍ → ℂ := fun z => Fz z z with hF
  have key : ∀ z₀, ∀ z ∈ V z₀, F z = Fz z₀ z := fun z₀ z hz => hag z z₀ z ⟨hVm z, hz⟩
  refine ⟨F, ?_, ?_, fun z => hFb z⟩
  · refine continuous_iff_continuousAt.2 fun z₀ => ?_
    refine (hFc z₀).continuousAt.congr ?_
    filter_upwards [(hVo z₀).mem_nhds (hVm z₀)] with z hz
    exact (key z₀ z hz).symm
  · obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
    have hall : ∀ᵐ w ∂(volume : Measure ℍ), ∀ z₀ ∈ T, w ∈ V z₀ → u' w = Fz z₀ w :=
      (ae_ball_iff hT).2 fun z₀ _ => hFa z₀
    filter_upwards [hall] with w hw
    have hmem : w ∈ ⋃ i ∈ T, V i := by
      rw [hTU]; exact mem_iUnion.2 ⟨w, hVm w⟩
    obtain ⟨z₀, hz₀, hwz⟩ := mem_iUnion₂.1 hmem
    rw [key z₀ w hwz, hw z₀ hz₀ hwz]

/-- **The Sobolev bound on `M` with the multiplicity factor** (Lemma `pc:g43`, with one Laplacian). -/
theorem sobolev_M_mult : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (u : (negLapMH Γ).domain),
      ∃ f : Surf Γ → ℂ, Continuous f ∧ f =ᵐ[surfMeasure Γ] ⇑(u : Lp ℂ 2 (surfMeasure Γ)) ∧
        ∀ x, ‖f x‖ₑ ≤ ENNReal.ofReal K * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)
          * ENNReal.ofReal (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖) := by
  obtain ⟨K, r, hK, hr, hrep⟩ := chart_rep_mult
  refine ⟨K, hK, ?_⟩
  intro Γ _ u
  obtain ⟨F, hFc, hFa, hFb⟩ := glue_rep_pt (u' := liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)))
    (B := fun z => K * (sqrtMult Γ z * (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖)))
    (fun z₀ => by
      obtain ⟨F, hFc, V, hV, hz, hae, hb⟩ := patch_rep_mult hr hrep Γ u z₀ (sqrtMult_nonneg Γ z₀) (orbitMult_le_sqrtMult Γ z₀)
      exact ⟨F, hFc, V, hV, hz, hae, hb z₀⟩)
  have hinv : ∀ (γ : Γ) (z : ℍ), F (γ • z) = F z := by
    intro γ
    have hcγ : Continuous fun z : ℍ => F (γ • z) := hFc.comp (continuous_const_smul γ)
    refine congrFun ((Continuous.ae_eq_iff_eq (volume : Measure ℍ) hcγ hFc).1 ?_)
    have h1 := (measurePreserving_smul γ (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hFa
    filter_upwards [h1, hFa] with z e1 e2
    have e1' : F (γ • z) = liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) (γ • z) := e1
    rw [e1', e2, liftM_smul]
  have hs : ∀ a b : ℍ, (MulAction.orbitRel Γ ℍ) a b → F a = F b := by
    rintro a b ⟨γ, rfl⟩
    exact hinv γ b
  refine ⟨Quotient.lift F hs, hFc.quotient_lift hs, ?_, ?_⟩
  · have hml : Measurable (Quotient.lift F hs : Surf Γ → ℂ) := measurable_from_quotient.2 hFc.measurable
    have hm : Measurable fun x : Surf Γ => Quotient.lift F hs x - (u : Lp ℂ 2 (surfMeasure Γ)) x :=
      hml.sub (Lp.stronglyMeasurable _).measurable
    have h := ae_eq_zero_of_lift Γ hm (by
      filter_upwards [hFa] with z hz
      show F z - liftM Γ (u : Lp ℂ 2 (surfMeasure Γ)) z = 0
      rw [hz, sub_self])
    filter_upwards [h] with x hx
    exact sub_eq_zero.1 hx
  · intro x
    induction x using Quotient.inductionOn with | _ z
    have h := hFb z
    show ‖F z‖ₑ ≤ ENNReal.ofReal K * (multM Γ (surfMk Γ z) : ℝ≥0∞) ^ (1 / 2 : ℝ)
      * ENNReal.ofReal (‖(u : Lp ℂ 2 (surfMeasure Γ))‖ + ‖negLapMH Γ u‖)
    rw [multM_mk, ← ofReal_sqrtMult, ← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul (mul_nonneg hK (sqrtMult_nonneg Γ z)), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (h.trans_eq (by ring))

end Qschubert
