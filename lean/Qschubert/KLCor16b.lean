import Qschubert.KLCor16a

/-!
# Interior regularity on `M`: the form step and the domain step

For nested real cutoffs `χ₂ ≺ χ₁ ≺ χ₀` with `χ₀` injective on orbits: `χ₁ ũ` lies in the form space (`cut_form`) and `χ₂ ũ` lies in `Dom(-Δ)` on `ℍ` (`cut_dom`), with bounds by `‖u‖ + ‖A u‖`
whose constants depend on the cutoffs only.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- If `G ↦ ⟪ΔG, v⟫` is bounded in `L²`, then `v ∈ Dom(-Δ)`, with `‖Δv‖` at most the bound. -/
theorem mem_dom_of_bound {v : L2H'} {B : ℝ} (hB0 : 0 ≤ B)
    (h : ∀ G : testFn, ‖⟪toL2 (lapTest G), v⟫_ℂ‖ ≤ B * ‖toL2 G‖) :
    ∃ hv : v ∈ negLapH.domain, ‖negLapH ⟨v, hv⟩‖ ≤ B := by
  let L : lapDomain →ₗ[ℂ] ℂ :=
    { toFun := fun x => ⟪v, toL2 (lapTest (toL2Equiv.symm x))⟫_ℂ
      map_add' := fun x y => by simp only [map_add, inner_add_right]
      map_smul' := fun c x => by simp only [map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul] }
  have hLb : ∀ x : lapDomain, ‖L x‖ ≤ B * ‖x‖ := fun x => by
    obtain ⟨G, rfl⟩ := toL2Equiv.surjective x
    show ‖⟪v, toL2 (lapTest (toL2Equiv.symm (toL2Equiv G)))⟫_ℂ‖ ≤ _
    rw [toL2Equiv.symm_apply_apply, norm_inner_symm]
    have e : ‖toL2Equiv G‖ = ‖toL2 G‖ := by rw [Submodule.coe_norm, coe_toL2Equiv]
    rw [e]; exact h G
  let Lc : lapDomain →L[ℂ] ℂ := L.mkContinuous B hLb
  let e : lapDomain →L[ℂ] L2H' := lapDomain.subtypeL
  have hd : DenseRange e := by
    rw [DenseRange, show Set.range e = (lapDomain : Set L2H') from Subtype.range_coe]
    exact negLap_hasDenseDomain
  have hu : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  let Λ : L2H' →L[ℂ] ℂ := Lc.extend e
  have hΛc : ∀ x : lapDomain, Λ (e x) = L x := fun x => ContinuousLinearMap.extend_eq Lc (e := e) hd hu x
  have hΛb : ‖Λ‖ ≤ B := by
    refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun q => ?_
    refine hd.induction_on q (isClosed_le Λ.continuous.norm (continuous_const.mul continuous_norm)) fun x => ?_
    rw [hΛc]
    exact hLb x
  set w : L2H' := (InnerProductSpace.toDual ℂ L2H').symm Λ with hw
  have hin : ∀ y, ⟪w, y⟫_ℂ = Λ y := fun y => InnerProductSpace.toDual_symm_apply
  have hweak : ∀ G : testFn, ⟪toL2 (lapTest G), v⟫_ℂ = ⟪toL2 G, w⟫_ℂ := fun G => by
    have h1 := hin (toL2 G)
    have e1 : Λ (toL2 G) = L (toL2Equiv G) := by
      rw [← hΛc]
      congr 1
    have e2 : L (toL2Equiv G) = ⟪v, toL2 (lapTest G)⟫_ℂ := by
      show ⟪v, toL2 (lapTest (toL2Equiv.symm (toL2Equiv G)))⟫_ℂ = _
      rw [toL2Equiv.symm_apply_apply]
    rw [e1, e2] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [inner_conj_symm] at h2
    exact h2.symm
  obtain ⟨hv, hn⟩ := mem_negLapH_of_weak hweak
  refine ⟨hv, ?_⟩
  rw [hn, norm_neg, hw, LinearIsometryEquiv.norm_map]
  exact hΛb

lemma norm_toL2_mulT_le (c Q : testFn) : ‖toL2 (mulT c Q)‖ ≤ supT c * ‖toL2 Q‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [toL2_ae (mulT c Q), toL2_ae Q] with z h1 h2
  rw [h1, h2, mulT_coe, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_supT c _) (norm_nonneg _)

/-- `θ = 1` where `c ≠ 0`. -/
def Absorbs (θ c : testFn) : Prop := ∀ w, (c : ℂ → ℂ) w ≠ 0 → (θ : ℂ → ℂ) w = 1

lemma mulT_absorb {θ c : testFn} (h : Absorbs θ c) (Q : testFn) : mulT θ (mulT c Q) = mulT c Q := by
  apply Subtype.ext; funext w
  show (θ : ℂ → ℂ) w * ((c : ℂ → ℂ) w * (Q : ℂ → ℂ) w) = (c : ℂ → ℂ) w * (Q : ℂ → ℂ) w
  by_cases hw : (c : ℂ → ℂ) w = 0
  · simp [hw]
  · rw [h w hw, one_mul]

/-- `θ = 1` on the closed support of `χ`. -/
def OneOn (θ χ : testFn) : Prop := ∀ w ∈ tsupport (χ : ℂ → ℂ), (θ : ℂ → ℂ) w = 1

lemma OneOn.vf {θ χ : testFn} (h : OneOn θ χ) (v : ℂ) : Absorbs θ (vfTest v χ) := fun w hw =>
  h w (tsupport_vfTest_sub v χ (subset_tsupport _ hw))

lemma OneOn.lap {θ χ : testFn} (h : OneOn θ χ) : Absorbs θ (lapTest χ) := fun w hw =>
  h w (tsupport_lapTest_sub χ (subset_tsupport _ hw))

lemma form_sq (ξ : FormSpace negLap) :
    ‖formVec 1 (Or.inl rfl) ξ‖ ^ 2 + ‖formVec Complex.I (Or.inr rfl) ξ‖ ^ 2 + ‖formIncl negLap ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have h := congrArg Complex.re (inner_formVec_add ξ ξ)
  have e1 : ∀ {E : Type _} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : E), ‖x‖ ^ 2 = (inner ℂ x x).re := fun x => by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  rw [Complex.add_re, Complex.sub_re, ← e1, ← e1, ← e1, ← e1] at h
  linarith

lemma norm_formVec_le' (v : ℂ) (hv : v = 1 ∨ v = Complex.I) (ξ : FormSpace negLap) : ‖formVec v hv ξ‖ ≤ ‖ξ‖ := by
  have h := form_sq ξ
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rcases hv with rfl | rfl
  · nlinarith [sq_nonneg ‖formVec Complex.I (Or.inr rfl) ξ‖, sq_nonneg ‖formIncl negLap ξ‖]
  · nlinarith [sq_nonneg ‖formVec 1 (Or.inl rfl) ξ‖, sq_nonneg ‖formIncl negLap ξ‖]

lemma norm_formIncl_le' (ξ : FormSpace negLap) : ‖formIncl negLap ξ‖ ≤ ‖ξ‖ := by
  have h := form_sq ξ
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  nlinarith [sq_nonneg ‖formVec Complex.I (Or.inr rfl) ξ‖, sq_nonneg ‖formVec 1 (Or.inl rfl) ξ‖]

/-- `‖⟪c · y∂_v G, ιξ⟫‖ ≤ (2 sup|c| + sup|y∂_v c|) ‖G‖ ‖ξ‖`. -/
lemma form_cross (v : ℂ) (hv : v = 1 ∨ v = Complex.I) (c G : testFn) (ξ : FormSpace negLap) :
    ‖⟪toL2 (mulT c (vfTest v G)), formIncl negLap ξ⟫_ℂ‖ ≤ (2 * supT c + supT (vfTest v c)) * (‖toL2 G‖ * ‖ξ‖) := by
  have e : mulT c (vfTest v G) = vfTest v (mulT c G) - mulT (vfTest v c) G := by
    rw [vf_mulT]; abel
  have h := inner_toL2_formVec v hv (mulT c G) ξ
  have e2 : ⟪toL2 (vfTest v (mulT c G)), formIncl negLap ξ⟫_ℂ
      = -⟪toL2 (mulT c G), formVec v hv ξ⟫_ℂ + ((v.im : ℝ) : ℂ) * ⟪toL2 (mulT c G), formIncl negLap ξ⟫_ℂ := by
    rw [h]; ring
  rw [e, map_sub, inner_sub_left, e2]
  have him : ‖((v.im : ℝ) : ℂ)‖ ≤ 1 := by
    rcases hv with rfl | rfl <;> simp
  have h1 : ‖⟪toL2 (mulT c G), formVec v hv ξ⟫_ℂ‖ ≤ supT c * ‖toL2 G‖ * ‖ξ‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_toL2_mulT_le c G) (norm_formVec_le' v hv ξ) (norm_nonneg _)
      (mul_nonneg (supT_nonneg c) (norm_nonneg _)))
  have h2 : ‖⟪toL2 (mulT c G), formIncl negLap ξ⟫_ℂ‖ ≤ supT c * ‖toL2 G‖ * ‖ξ‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_toL2_mulT_le c G) (norm_formIncl_le' ξ) (norm_nonneg _)
      (mul_nonneg (supT_nonneg c) (norm_nonneg _)))
  have h3 : ‖⟪toL2 (mulT (vfTest v c) G), formIncl negLap ξ⟫_ℂ‖ ≤ supT (vfTest v c) * ‖toL2 G‖ * ‖ξ‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_toL2_mulT_le _ G) (norm_formIncl_le' ξ) (norm_nonneg _)
      (mul_nonneg (supT_nonneg _) (norm_nonneg _)))
  have h4 : ‖((v.im : ℝ) : ℂ) * ⟪toL2 (mulT c G), formIncl negLap ξ⟫_ℂ‖ ≤ supT c * ‖toL2 G‖ * ‖ξ‖ := by
    rw [norm_mul]
    calc _ ≤ 1 * ‖⟪toL2 (mulT c G), formIncl negLap ξ⟫_ℂ‖ := mul_le_mul_of_nonneg_right him (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h2
  calc _ ≤ ‖-⟪toL2 (mulT c G), formVec v hv ξ⟫_ℂ‖ + ‖((v.im : ℝ) : ℂ) * ⟪toL2 (mulT c G), formIncl negLap ξ⟫_ℂ‖ + ‖⟪toL2 (mulT (vfTest v c) G), formIncl negLap ξ⟫_ℂ‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ supT c * ‖toL2 G‖ * ‖ξ‖ + supT c * ‖toL2 G‖ * ‖ξ‖ + supT (vfTest v c) * ‖toL2 G‖ * ‖ξ‖ := by
        rw [norm_neg]; gcongr
    _ = _ := by ring

section nested

variable {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ]

local notation "L2M" => Lp ℂ 2 (surfMeasure Γ)

/-- **The localized equation.** -/
theorem cut_lap {χ θ : testFn} {μ : ℝ} (hχ : IsRealT χ) (hθ : IsRealT θ) (hi : CutB Γ χ μ) (hj : CutB Γ θ μ) (h1 : OneOn θ χ)
    (u : (negLapMH Γ).domain) (Q : testFn) :
    ⟪toL2 (lapTest Q), cutV hi (u : L2M)⟫_ℂ = -⟪toL2 Q, cutV hi (negLapMH Γ u)⟫_ℂ
      - ⟪toL2 (mulT (lapTest χ) Q), cutV hj (u : L2M)⟫_ℂ
      - 2 * ⟪toL2 (mulT (vfTest 1 χ) (vfTest 1 Q)), cutV hj (u : L2M)⟫_ℂ
      - 2 * ⟪toL2 (mulT (vfTest Complex.I χ) (vfTest Complex.I Q)), cutV hj (u : L2M)⟫_ℂ := by
  have hprod := lapTest_mulT χ Q
  have e1 : mulT χ (lapTest Q) = lapTest (mulT χ Q) - mulT (lapTest χ) Q
      - (2 : ℂ) • (mulT (vfTest 1 χ) (vfTest 1 Q) + mulT (vfTest Complex.I χ) (vfTest Complex.I Q)) := by
    rw [hprod]; abel
  have hA : ∀ (c : testFn), Absorbs θ c → ∀ P : testFn, ⟪toL2 (mulT c P), cutV hj (u : L2M)⟫_ℂ = ⟪perioT Γ (mulT c P), (u : L2M)⟫_ℂ :=
    fun c hc P => by rw [cut_pair hθ hj, mulT_absorb hc]
  have eL : ∀ F, perioT Γ F = perioTLin Γ F := fun _ => rfl
  rw [cut_pair hχ hi, e1, cut_pair hχ hi, hA _ h1.lap, hA _ (h1.vf 1), hA _ (h1.vf Complex.I)]
  have hW := weak_tests u (mulT χ Q)
  rw [← hW]
  simp only [eL, map_sub, map_smul, map_add, inner_sub_left, inner_smul_left, inner_add_left]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  rw [h2]
  ring

/-- The constant of the form step. -/
noncomputable def Kform (χ θ : testFn) : ℝ :=
  supT χ + (supT (lapTest χ) + 2 * supT (vfTest 1 χ) + 2 * supT (vfTest Complex.I χ)) * supT θ

lemma Kform_nonneg (χ θ : testFn) : 0 ≤ Kform χ θ := by
  unfold Kform
  have := supT_nonneg χ
  have := supT_nonneg (lapTest χ)
  have := supT_nonneg (vfTest 1 χ)
  have := supT_nonneg (vfTest Complex.I χ)
  have := supT_nonneg θ
  positivity

/-- **The form step.** -/
theorem cut_form {χ θ : testFn} {μ : ℝ} (hχ : IsRealT χ) (hθ : IsRealT θ) (hi : CutB Γ χ μ) (hj : CutB Γ θ μ) (h1 : OneOn θ χ)
    (u : (negLapMH Γ).domain) :
    ∃ ξ : FormSpace negLap, formIncl negLap ξ = cutV hi (u : L2M) ∧
      ‖ξ‖ ≤ Kform χ θ * (μ * ‖(u : L2M)‖ + μ * ‖negLapMH Γ u‖) := by
  have hU := mul_nonneg hi.nonneg (norm_nonneg (u : L2M))
  have hW := mul_nonneg hi.nonneg (norm_nonneg (negLapMH Γ u))
  have hB0 := mul_nonneg (Kform_nonneg χ θ) (add_nonneg hU hW)
  refine exists_form_of_bound hB0 fun P => ?_
  rw [norm_inner_symm, inner_sub_left, cut_lap hχ hθ hi hj h1]
  set F := Real.sqrt (‖toL2 P‖ ^ 2 + ‖toL2 (vfTest 1 P)‖ ^ 2 + ‖toL2 (vfTest Complex.I P)‖ ^ 2) with hF
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hP : ‖toL2 P‖ ≤ F := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖toL2 (vfTest 1 P)‖, sq_nonneg ‖toL2 (vfTest Complex.I P)‖])
  have hX : ‖toL2 (vfTest 1 P)‖ ≤ F := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖toL2 P‖, sq_nonneg ‖toL2 (vfTest Complex.I P)‖])
  have hY : ‖toL2 (vfTest Complex.I P)‖ ≤ F := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖toL2 P‖, sq_nonneg ‖toL2 (vfTest 1 P)‖])
  have hcu : ‖cutV hi (u : L2M)‖ ≤ supT χ * (μ * ‖(u : L2M)‖) := (norm_cutV_le hi _).trans_eq (mul_assoc _ _ _)
  have hcw : ‖cutV hi (negLapMH Γ u)‖ ≤ supT χ * (μ * ‖negLapMH Γ u‖) := (norm_cutV_le hi _).trans_eq (mul_assoc _ _ _)
  have hcθ : ‖cutV hj (u : L2M)‖ ≤ supT θ * (μ * ‖(u : L2M)‖) := (norm_cutV_le hj _).trans_eq (mul_assoc _ _ _)
  set U := μ * ‖(u : L2M)‖
  set W := μ * ‖negLapMH Γ u‖
  have hSχ := supT_nonneg χ
  have hSθ := supT_nonneg θ
  have a1 : ‖⟪toL2 P, cutV hi (u : L2M)⟫_ℂ‖ ≤ F * (supT χ * U) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hP hcu (norm_nonneg _) hF0)
  have a2 : ‖⟪toL2 P, cutV hi (negLapMH Γ u)⟫_ℂ‖ ≤ F * (supT χ * W) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hP hcw (norm_nonneg _) hF0)
  have bd : ∀ (c Q : testFn), ‖toL2 Q‖ ≤ F → ‖⟪toL2 (mulT c Q), cutV hj (u : L2M)⟫_ℂ‖ ≤ supT c * F * (supT θ * U) := fun c Q hQ =>
    (norm_inner_le_norm _ _).trans (mul_le_mul ((norm_toL2_mulT_le c Q).trans (mul_le_mul_of_nonneg_left hQ (supT_nonneg c))) hcθ
      (norm_nonneg _) (mul_nonneg (supT_nonneg c) hF0))
  have a3 := bd (lapTest χ) P hP
  have a4 := bd (vfTest 1 χ) (vfTest 1 P) hX
  have a5 := bd (vfTest Complex.I χ) (vfTest Complex.I P) hY
  set A1 := ⟪toL2 P, cutV hi (u : L2M)⟫_ℂ
  set A2 := ⟪toL2 P, cutV hi (negLapMH Γ u)⟫_ℂ
  set A3 := ⟪toL2 (mulT (lapTest χ) P), cutV hj (u : L2M)⟫_ℂ
  set A4 := ⟪toL2 (mulT (vfTest 1 χ) (vfTest 1 P)), cutV hj (u : L2M)⟫_ℂ
  set A5 := ⟪toL2 (mulT (vfTest Complex.I χ) (vfTest Complex.I P)), cutV hj (u : L2M)⟫_ℂ
  have eS : A1 - (-A2 - A3 - 2 * A4 - 2 * A5) = A1 + A2 + A3 + 2 * A4 + 2 * A5 := by ring
  rw [eS]
  have tri : ‖A1 + A2 + A3 + 2 * A4 + 2 * A5‖ ≤ ‖A1‖ + ‖A2‖ + ‖A3‖ + 2 * ‖A4‖ + 2 * ‖A5‖ := by
    calc _ ≤ ‖A1 + A2 + A3 + 2 * A4‖ + ‖2 * A5‖ := norm_add_le _ _
      _ ≤ ‖A1 + A2 + A3‖ + ‖2 * A4‖ + ‖2 * A5‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A1 + A2‖ + ‖A3‖ + ‖2 * A4‖ + ‖2 * A5‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖A1‖ + ‖A2‖ + ‖A3‖ + ‖2 * A4‖ + ‖2 * A5‖ := by gcongr; exact norm_add_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_ofNat]
  refine tri.trans ?_
  have hD0 : 0 ≤ (supT (lapTest χ) + 2 * supT (vfTest 1 χ) + 2 * supT (vfTest Complex.I χ)) * supT θ * U := by
    have := supT_nonneg (lapTest χ)
    have := supT_nonneg (vfTest 1 χ)
    have := supT_nonneg (vfTest Complex.I χ)
    positivity
  have e3 : F * ((supT (lapTest χ) + 2 * supT (vfTest 1 χ) + 2 * supT (vfTest Complex.I χ)) * supT θ * W) ≥ 0 := by
    have := supT_nonneg (lapTest χ)
    have := supT_nonneg (vfTest 1 χ)
    have := supT_nonneg (vfTest Complex.I χ)
    positivity
  unfold Kform
  nlinarith

/-- The constant of the domain step. -/
noncomputable def Kdom (χ₂ χ₁ χ₀ : testFn) : ℝ :=
  supT χ₂ + (supT (lapTest χ₂) + 2 * (2 * supT (vfTest 1 χ₂) + supT (vfTest 1 (vfTest 1 χ₂)))
    + 2 * (2 * supT (vfTest Complex.I χ₂) + supT (vfTest Complex.I (vfTest Complex.I χ₂)))) * Kform χ₁ χ₀

lemma Kdom_nonneg (χ₂ χ₁ χ₀ : testFn) : 0 ≤ Kdom χ₂ χ₁ χ₀ := by
  unfold Kdom
  have := supT_nonneg χ₂
  have := supT_nonneg (lapTest χ₂)
  have := supT_nonneg (vfTest 1 χ₂)
  have := supT_nonneg (vfTest Complex.I χ₂)
  have := supT_nonneg (vfTest 1 (vfTest 1 χ₂))
  have := supT_nonneg (vfTest Complex.I (vfTest Complex.I χ₂))
  have := Kform_nonneg χ₁ χ₀
  positivity

/-- **The domain step.** -/
theorem cut_dom {χ₂ χ₁ χ₀ : testFn} {μ : ℝ} (h2R : IsRealT χ₂) (h1R : IsRealT χ₁) (h0R : IsRealT χ₀) (hi2 : CutB Γ χ₂ μ) (hi1 : CutB Γ χ₁ μ)
    (hi0 : CutB Γ χ₀ μ) (h21 : OneOn χ₁ χ₂) (h10 : OneOn χ₀ χ₁) (u : (negLapMH Γ).domain) :
    ∃ hv : cutV hi2 (u : L2M) ∈ negLapH.domain,
      ‖negLapH ⟨cutV hi2 (u : L2M), hv⟩‖ ≤ Kdom χ₂ χ₁ χ₀ * (μ * ‖(u : L2M)‖ + μ * ‖negLapMH Γ u‖) := by
  obtain ⟨ξ, hξ, hξb⟩ := cut_form h1R h0R hi1 hi0 h10 u
  have hU := mul_nonneg hi2.nonneg (norm_nonneg (u : L2M))
  have hW := mul_nonneg hi2.nonneg (norm_nonneg (negLapMH Γ u))
  have hB0 := mul_nonneg (Kdom_nonneg χ₂ χ₁ χ₀) (add_nonneg hU hW)
  refine mem_dom_of_bound hB0 fun G => ?_
  rw [cut_lap h2R h1R hi2 hi1 h21, ← hξ]
  have hcw : ‖cutV hi2 (negLapMH Γ u)‖ ≤ supT χ₂ * (μ * ‖negLapMH Γ u‖) := (norm_cutV_le hi2 _).trans_eq (mul_assoc _ _ _)
  set U := μ * ‖(u : L2M)‖
  set W := μ * ‖negLapMH Γ u‖
  set g := ‖toL2 G‖ with hg
  have hg0 : 0 ≤ g := norm_nonneg _
  have a1 : ‖⟪toL2 G, cutV hi2 (negLapMH Γ u)⟫_ℂ‖ ≤ g * (supT χ₂ * W) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hcw hg0)
  have a2 : ‖⟪toL2 (mulT (lapTest χ₂) G), formIncl negLap ξ⟫_ℂ‖ ≤ supT (lapTest χ₂) * g * ‖ξ‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (norm_toL2_mulT_le _ G) (norm_formIncl_le' ξ) (norm_nonneg _)
      (mul_nonneg (supT_nonneg _) hg0))
  have a3 := form_cross 1 (Or.inl rfl) (vfTest 1 χ₂) G ξ
  have a4 := form_cross Complex.I (Or.inr rfl) (vfTest Complex.I χ₂) G ξ
  set A1 := ⟪toL2 G, cutV hi2 (negLapMH Γ u)⟫_ℂ
  set A2 := ⟪toL2 (mulT (lapTest χ₂) G), formIncl negLap ξ⟫_ℂ
  set A3 := ⟪toL2 (mulT (vfTest 1 χ₂) (vfTest 1 G)), formIncl negLap ξ⟫_ℂ
  set A4 := ⟪toL2 (mulT (vfTest Complex.I χ₂) (vfTest Complex.I G)), formIncl negLap ξ⟫_ℂ
  have tri : ‖-A1 - A2 - 2 * A3 - 2 * A4‖ ≤ ‖A1‖ + ‖A2‖ + 2 * ‖A3‖ + 2 * ‖A4‖ := by
    calc _ ≤ ‖-A1 - A2 - 2 * A3‖ + ‖2 * A4‖ := norm_sub_le _ _
      _ ≤ ‖-A1 - A2‖ + ‖2 * A3‖ + ‖2 * A4‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ ‖-A1‖ + ‖A2‖ + ‖2 * A3‖ + ‖2 * A4‖ := by gcongr; exact norm_sub_le _ _
      _ = _ := by simp only [norm_mul, norm_neg, Complex.norm_ofNat]
  refine tri.trans ?_
  set D := supT (lapTest χ₂) + 2 * (2 * supT (vfTest 1 χ₂) + supT (vfTest 1 (vfTest 1 χ₂)))
    + 2 * (2 * supT (vfTest Complex.I χ₂) + supT (vfTest Complex.I (vfTest Complex.I χ₂))) with hD
  have hD0 : 0 ≤ D := by
    have := supT_nonneg (lapTest χ₂)
    have := supT_nonneg (vfTest 1 χ₂)
    have := supT_nonneg (vfTest Complex.I χ₂)
    have := supT_nonneg (vfTest 1 (vfTest 1 χ₂))
    have := supT_nonneg (vfTest Complex.I (vfTest Complex.I χ₂))
    positivity
  have hsum : ‖A1‖ + ‖A2‖ + 2 * ‖A3‖ + 2 * ‖A4‖ ≤ g * (supT χ₂ * W) + D * (g * ‖ξ‖) := by
    rw [hD]; nlinarith
  refine hsum.trans ?_
  have h3 : D * (g * ‖ξ‖) ≤ D * (g * (Kform χ₁ χ₀ * (U + W))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξb hg0) hD0
  have h4 : g * (supT χ₂ * W) ≤ g * (supT χ₂ * (U + W)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) (supT_nonneg χ₂)) hg0
  have e : Kdom χ₂ χ₁ χ₀ * (U + W) * g = g * (supT χ₂ * (U + W)) + D * (g * (Kform χ₁ χ₀ * (U + W))) := by
    unfold Kdom; rw [← hD]; ring
  rw [e]
  linarith

end nested

end Qschubert
