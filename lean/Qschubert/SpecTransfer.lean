import Qschubert.LemmaC
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Transferring the functional calculus through an intertwining operator

Setting: `A` self-adjoint on `H` with spectral measure `P`, `V : H →L L²(X, μ)` bounded, `m : X → ℝ`
measurable, and `V (A x) = m · V x` (a.e.) for `x ∈ Dom A` (`hV`). No isometry or surjectivity of `V` is
assumed, and nothing is assumed about the multiplication operator by `m`.

`IsGood f`: `V (∫ f dP η) = (f ∘ m) · V η` a.e., for every `η`.

* `isGood_resolvent`: `(x - c)⁻¹` is good for non-real `c` (from `hV` and `pmapIntegral_sub_smul_integral_inv`).
* `IsGood.mul`, `.add`, `.smul`, `isGood_one`: closure under the algebra operations (`integral_mul`).
* `isGood_of_uniform`: closure under uniform limits (`norm_integral_le`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

section transfer

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (V : H →L[ℂ] Lp ℂ 2 μ) (m : X → ℝ)

/-- `V (∫ f dP η) = (f ∘ m) · V η` a.e. for every `η`. -/
def IsGood (f : ℝ → ℂ) : Prop :=
  ∀ η : H, ((V ((spectralMeasure hA).integral f η) : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
    fun p => f (m p) * (V η : X → ℂ) p

variable {hA V m}

lemma isGood_one : IsGood hA V m 1 := by
  intro η
  rw [ProjectionValuedMeasure.integral_one]
  exact Eventually.of_forall fun p => by simp

lemma IsGood.add {f g : ℝ → ℂ} (hf : f ∈ BddMeasurable ℝ) (hg : g ∈ BddMeasurable ℝ)
    (hgf : IsGood hA V m f) (hgg : IsGood hA V m g) : IsGood hA V m (f + g) := by
  intro η
  rw [ProjectionValuedMeasure.integral_add _ hf hg, ContinuousLinearMap.add_apply, map_add]
  filter_upwards [Lp.coeFn_add (V ((spectralMeasure hA).integral f η)) (V ((spectralMeasure hA).integral g η)),
    hgf η, hgg η] with p h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.add_apply]; ring

lemma IsGood.smul {f : ℝ → ℂ} (hf : f ∈ BddMeasurable ℝ) (c : ℂ) (hgf : IsGood hA V m f) :
    IsGood hA V m (c • f) := by
  intro η
  rw [ProjectionValuedMeasure.integral_smul _ c hf, ContinuousLinearMap.smul_apply, map_smul]
  filter_upwards [Lp.coeFn_smul c (V ((spectralMeasure hA).integral f η)), hgf η] with p h1 h2
  rw [h1, Pi.smul_apply, h2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]; ring

lemma IsGood.mul {f g : ℝ → ℂ} (hf : f ∈ BddMeasurable ℝ) (hg : g ∈ BddMeasurable ℝ)
    (hgf : IsGood hA V m f) (hgg : IsGood hA V m g) : IsGood hA V m (f * g) := by
  intro η
  rw [ProjectionValuedMeasure.integral_mul _ hf hg, ContinuousLinearMap.mul_apply]
  filter_upwards [hgf ((spectralMeasure hA).integral g η), hgg η] with p h1 h2
  rw [h1, h2, Pi.mul_apply]; ring

variable (hV : ∀ x : A.domain, ((V (A x) : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
    fun p => (m p : ℂ) * (V (x : H) : X → ℂ) p)
include hV

/-- The resolvent `(x - c)⁻¹` is good for non-real `c`. -/
lemma isGood_resolvent {c : ℂ} (hc : c.im ≠ 0) : IsGood hA V m fun x : ℝ => ((x : ℂ) - c)⁻¹ := by
  intro η
  set P := spectralMeasure hA
  set ψ := P.integral (fun x : ℝ => ((x : ℂ) - c)⁻¹) η
  obtain ⟨hψ, he⟩ := pmapIntegral_sub_smul_integral_inv P Complex.measurable_ofReal
    (fun x => Complex.ofReal_im x) hc η
  have e := pmapIntegral_spectralMeasure hA
  have hdom : ψ ∈ A.domain := by rw [← e]; exact hψ
  obtain ⟨_, hval⟩ := LinearPMap.ext_iff.mp e
  have hA' : pmapIntegral P (fun x : ℝ => (x : ℂ)) ⟨ψ, hψ⟩ = A ⟨ψ, hdom⟩ := hval (x := ψ) (hf := hψ) (hg := hdom)
  rw [hA'] at he
  -- `V η = V (A ψ) - c V ψ = (m - c) V ψ`
  have hVη : (V η : X → ℂ) =ᵐ[μ] fun p => ((m p : ℂ) - c) * (V ψ : X → ℂ) p := by
    rw [← he, map_sub, map_smul]
    filter_upwards [Lp.coeFn_sub (V (A ⟨ψ, hdom⟩)) (c • V ψ), Lp.coeFn_smul c (V ψ), hV ⟨ψ, hdom⟩]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul]; ring
  filter_upwards [hVη] with p hp
  have hne : (m p : ℂ) - c ≠ 0 := fun h => hc (by simpa using congrArg Complex.im h)
  rw [hp, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

omit hV in
/-- **Uniform limits of good functions are good.** -/
lemma isGood_of_uniform (hm : Measurable m) {φ : ℝ → ℂ} (hφ : φ ∈ BddMeasurable ℝ)
    (h : ∀ ε > 0, ∃ f : ℝ → ℂ, f ∈ BddMeasurable ℝ ∧ IsGood hA V m f ∧ ∀ x, ‖f x - φ x‖ ≤ ε) :
    IsGood hA V m φ := by
  intro η
  set P := spectralMeasure hA
  have hφm : Measurable φ := ((mem_bddMeasurable).1 hφ).1
  set D : X → ℂ := fun p => (V (P.integral φ η) : X → ℂ) p - φ (m p) * (V η : X → ℂ) p
  have hDm : AEStronglyMeasurable D μ :=
    (Lp.aestronglyMeasurable _).sub ((hφm.comp hm).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
  set K : ℝ := ‖V‖ * ‖η‖ + ‖V η‖
  have hK : 0 ≤ K := by positivity
  have hb : ∀ ε > 0, eLpNorm D 2 μ ≤ ENNReal.ofReal (ε * K) := by
    intro ε hε
    obtain ⟨f, hfB, hfG, hfε⟩ := h ε hε
    have hfm : Measurable f := ((mem_bddMeasurable).1 hfB).1
    have hdB : φ - f ∈ BddMeasurable ℝ := (BddMeasurable ℝ).sub_mem hφ hfB
    have hsplit : P.integral φ = P.integral (φ - f) + P.integral f := by
      rw [← ProjectionValuedMeasure.integral_add _ hdB hfB, sub_add_cancel]
    set E1 : X → ℂ := (V (P.integral (φ - f) η) : X → ℂ)
    set E2 : X → ℂ := fun p => (f (m p) - φ (m p)) * (V η : X → ℂ) p
    have hDE : D =ᵐ[μ] E1 + E2 := by
      have hV1 : V (P.integral φ η) = V (P.integral (φ - f) η) + V (P.integral f η) := by
        rw [hsplit, ContinuousLinearMap.add_apply, map_add]
      filter_upwards [Lp.coeFn_add (V (P.integral (φ - f) η)) (V (P.integral f η)), hfG η] with p h1 h2
      simp only [D, E1, E2, Pi.add_apply]
      rw [hV1, h1, Pi.add_apply, h2]; ring
    have hE1 : eLpNorm E1 2 μ ≤ ENNReal.ofReal (ε * (‖V‖ * ‖η‖)) := by
      rw [← Lp.enorm_def, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hI : ‖P.integral (φ - f)‖ ≤ ε := by
        refine (ProjectionValuedMeasure.norm_integral_le _ hdB).trans (ciSup_le fun x => ?_)
        rw [Pi.sub_apply, norm_sub_rev]; exact hfε x
      calc ‖V (P.integral (φ - f) η)‖ ≤ ‖V‖ * ‖P.integral (φ - f) η‖ := V.le_opNorm _
        _ ≤ ‖V‖ * (‖P.integral (φ - f)‖ * ‖η‖) :=
            mul_le_mul_of_nonneg_left ((P.integral (φ - f)).le_opNorm η) (norm_nonneg _)
        _ ≤ ‖V‖ * (ε * ‖η‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hI (norm_nonneg _)) (norm_nonneg _)
        _ = ε * (‖V‖ * ‖η‖) := by ring
    have hE2 : eLpNorm E2 2 μ ≤ ENNReal.ofReal (ε * ‖V η‖) := by
      have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (c := ε) (f := E2) (g := (V η : X → ℂ))
        (((hfm.comp hm).sub (hφm.comp hm)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
        (Eventually.of_forall fun p => by
          simp only [E2, norm_mul]
          exact mul_le_mul_of_nonneg_right (hfε (m p)) (norm_nonneg _)) 2
      rw [← Lp.enorm_def, ← ofReal_norm] at hle
      rw [ENNReal.ofReal_mul hε.le]
      exact hle
    calc eLpNorm D 2 μ = eLpNorm (E1 + E2) 2 μ := eLpNorm_congr_ae hDE
      _ ≤ eLpNorm E1 2 μ + eLpNorm E2 2 μ :=
          eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal (ε * (‖V‖ * ‖η‖)) + ENNReal.ofReal (ε * ‖V η‖) := add_le_add hE1 hE2
      _ = ENNReal.ofReal (ε * K) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have h0 : eLpNorm D 2 μ = 0 := by
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) bot_le
    rw [zero_add]
    have hδ' : (0 : ℝ) < δ / (K + 1) := by positivity
    calc eLpNorm D 2 μ ≤ ENNReal.ofReal (δ / (K + 1) * K) := hb _ hδ'
      _ ≤ ENNReal.ofReal δ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [NNReal.coe_nonneg δ]
      _ = δ := ENNReal.ofReal_coe_nnreal
  have hD0 := (eLpNorm_eq_zero_iff (by norm_num)).1 h0
  filter_upwards [hD0] with p hp
  simp only [D, Pi.zero_apply] at hp
  exact sub_eq_zero.1 hp

end transfer

/-! ### Stone–Weierstrass through the Cayley map -/

/-- The unit circle. -/
abbrev Circ : Type := Metric.sphere (0 : ℂ) 1

instance : CompactSpace Circ := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

/-- The Cayley map `x ↦ (x + i)/(x - i)` into the circle. -/
noncomputable def cay (x : ℝ) : Circ := ⟨cayleyMap x, by simpa using (cayleyMap_mem x).1⟩

lemma continuous_cay : Continuous cay := continuous_cayleyMap.subtype_mk _

lemma cay_ne_one (x : ℝ) : ((cay x : Circ) : ℂ) ≠ 1 := (cayleyMap_mem x).2

/-- The coordinate `z` on the circle. -/
noncomputable def circZ : C(Circ, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

lemma bdd_comp_cay (q : C(Circ, ℂ)) : (fun x => q (cay x)) ∈ BddMeasurable ℝ :=
  (mem_bddMeasurable).2 ⟨(q.continuous.comp continuous_cay).measurable, ‖q‖, fun x => q.norm_coe_le_norm _⟩

lemma cayleyMap_eq (x : ℝ) : cayleyMap x = 1 + 2 * Complex.I * ((x : ℂ) - Complex.I)⁻¹ := by
  have h : (x : ℂ) - Complex.I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  rw [cayleyMap]; field_simp; ring

lemma conj_cayleyMap_eq (x : ℝ) :
    (starRingEnd ℂ) (cayleyMap x) = 1 + (-2 * Complex.I) * ((x : ℂ) - (-Complex.I))⁻¹ := by
  have h : (x : ℂ) + Complex.I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  rw [cayleyMap, map_div₀, map_add, map_sub, Complex.conj_ofReal, Complex.conj_I, sub_neg_eq_add]
  field_simp; ring

/-- The function on the circle `u ↦ φ(cayleyInv u)`, `1 ↦ 0`. -/
noncomputable def circFun (φ : ℝ → ℂ) (u : Circ) : ℂ := if (u : ℂ) = 1 then 0 else φ (cayleyInv u)

lemma circFun_cay (φ : ℝ → ℂ) (x : ℝ) : circFun φ (cay x) = φ x := by
  rw [circFun, if_neg (cay_ne_one x)]; exact congrArg φ (cayleyInv_cayleyMap x)

lemma continuous_circFun {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : Tendsto φ (cocompact ℝ) (𝓝 0)) :
    Continuous (circFun φ) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  by_cases hu : (u : ℂ) = 1
  · -- near `1`, `|cayleyInv v| = ‖v + 1‖/‖v - 1‖` is large
    rw [ContinuousAt, show circFun φ u = 0 by rw [circFun, if_pos hu]]
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hset : {x : ℝ | ‖φ x‖ < ε} ∈ cocompact ℝ := by
      have := hφ0 (Metric.ball_mem_nhds (0 : ℂ) hε)
      simpa [Metric.ball, dist_eq_norm] using this
    obtain ⟨t, htc, hts⟩ := mem_cocompact.1 hset
    obtain ⟨R, hR⟩ := htc.isBounded.subset_closedBall 0
    set δ := min 1 (1 / (|R| + 1))
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    filter_upwards [Metric.ball_mem_nhds u hδ] with v hv
    rw [dist_eq_norm]
    by_cases hv1 : (v : ℂ) = 1
    · rw [circFun, if_pos hv1, sub_zero, norm_zero]; exact hε
    · rw [circFun, if_neg hv1, sub_zero]
      have hvc : (v : ℂ) ∈ unitCircleMinusOne := ⟨by simpa using v.2, hv1⟩
      have hd : ‖(v : ℂ) - 1‖ < δ := by
        have : dist v u < δ := hv
        rw [Subtype.dist_eq, dist_eq_norm, hu] at this; exact this
      have hd0 : 0 < ‖(v : ℂ) - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hv1)
      have hp1 : 1 ≤ ‖(v : ℂ) + 1‖ := by
        have h2 : ‖(2 : ℂ)‖ ≤ ‖(v : ℂ) + 1‖ + ‖(v : ℂ) - 1‖ := by
          calc ‖(2 : ℂ)‖ = ‖((v : ℂ) + 1) - ((v : ℂ) - 1)‖ := by congr 1; ring
            _ ≤ _ := norm_sub_le _ _
        have : δ ≤ 1 := min_le_left _ _
        rw [Complex.norm_two] at h2; linarith
      have habs : |cayleyInv v| = ‖(v : ℂ) + 1‖ / ‖(v : ℂ) - 1‖ := by
        rw [← Real.norm_eq_abs, ← Complex.norm_real, cayleyInv_ofReal hvc, norm_div, norm_mul, Complex.norm_I, one_mul]
      have hbig : |R| < |cayleyInv v| := by
        rw [habs, lt_div_iff₀ hd0]
        have h1 : ‖(v : ℂ) - 1‖ < 1 / (|R| + 1) := lt_of_lt_of_le hd (min_le_right _ _)
        rw [lt_div_iff₀ (by positivity)] at h1
        nlinarith [abs_nonneg R]
      have hnot : (cayleyInv v) ∉ t := by
        intro hmem
        have := hR hmem
        rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
        linarith [le_abs_self R]
      exact hts hnot
  · -- away from `1`, `circFun φ` is `φ ∘ cayleyInv`
    have hopen : IsOpen {v : Circ | (v : ℂ) ≠ 1} :=
      isOpen_ne_fun continuous_subtype_val continuous_const
    have heq : circFun φ =ᶠ[𝓝 u] fun v => φ (cayleyInv v) := by
      filter_upwards [hopen.mem_nhds hu] with v hv
      rw [circFun, if_neg hv]
    refine ContinuousAt.congr ?_ heq.symm
    have hden : (u : ℂ) - 1 ≠ 0 := sub_ne_zero.2 hu
    have hc : ContinuousAt (fun w : ℂ => cayleyInv w) (u : ℂ) := by
      unfold cayleyInv
      exact Complex.continuous_re.continuousAt.comp
        ((continuousAt_const.mul (continuousAt_id.add continuousAt_const)).div
          (continuousAt_id.sub continuousAt_const) hden)
    exact hφc.continuousAt.comp (hc.comp continuous_subtype_val.continuousAt)

section transfer2

variable {A : H →ₗ.[ℂ] H} {hA : IsSelfAdjoint A} {V : H →L[ℂ] Lp ℂ 2 μ} {m : X → ℝ}

lemma IsGood.congr {f g : ℝ → ℂ} (h : IsGood hA V m f) (hfg : f = g) : IsGood hA V m g := hfg ▸ h

variable (hV : ∀ x : A.domain, ((V (A x) : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ]
    fun p => (m p : ℂ) * (V (x : H) : X → ℂ) p)
include hV

lemma isGood_star_adjoin {q : C(Circ, ℂ)} (hq : q ∈ StarAlgebra.adjoin ℂ ({circZ} : Set C(Circ, ℂ))) :
    IsGood hA V m (fun x => q (cay x)) := by
  rw [← StarSubalgebra.mem_toSubalgebra, StarAlgebra.adjoin_toSubalgebra] at hq
  have hrB : ∀ c : ℂ, c.im ≠ 0 → (fun x : ℝ => ((x : ℂ) - c)⁻¹) ∈ BddMeasurable ℝ := by
    intro c hc
    refine (mem_bddMeasurable).2 ⟨(Complex.measurable_ofReal.sub_const _).inv, |c.im|⁻¹, fun x => ?_⟩
    rw [norm_inv]
    exact inv_anti₀ (abs_pos.2 hc) (by simpa using Complex.abs_im_le_norm ((x : ℂ) - c))
  have hone : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := (mem_bddMeasurable).2 ⟨measurable_const, 1, fun x => by simp⟩
  have g1 : IsGood hA V m 1 := isGood_one
  have gr : ∀ c : ℂ, c.im ≠ 0 → IsGood hA V m (fun x : ℝ => ((x : ℂ) - c)⁻¹) :=
    fun c hc => isGood_resolvent (hA := hA) hV hc
  induction hq using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · rw [Set.mem_singleton_iff.1 hx]
      have hg := g1.add hone ((BddMeasurable ℝ).smul_mem _ (hrB Complex.I (by simp)))
        ((gr Complex.I (by simp)).smul (hrB Complex.I (by simp)) (2 * Complex.I))
      refine hg.congr ?_
      funext x
      simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, circZ, ContinuousMap.coe_mk, cay]
      rw [cayleyMap_eq]
    · rw [Set.mem_star, Set.mem_singleton_iff] at hx
      have hx' : x = star circZ := by rw [← hx, star_star]
      rw [hx']
      have hg := g1.add hone ((BddMeasurable ℝ).smul_mem _ (hrB (-Complex.I) (by simp)))
        ((gr (-Complex.I) (by simp)).smul (hrB (-Complex.I) (by simp)) (-2 * Complex.I))
      refine hg.congr ?_
      funext x
      simp only [Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, ContinuousMap.star_apply, circZ,
        ContinuousMap.coe_mk, cay]
      rw [show star (cayleyMap x) = (starRingEnd ℂ) (cayleyMap x) from rfl, conj_cayleyMap_eq]
  | algebraMap r =>
    have hg := g1.smul hone r
    refine hg.congr ?_
    funext x; simp
  | add f g _ _ hf hg => exact (hf.add (bdd_comp_cay f) (bdd_comp_cay g) hg).congr (by funext x; simp)
  | mul f g _ _ hf hg => exact (hf.mul (bdd_comp_cay f) (bdd_comp_cay g) hg).congr (by funext x; simp)

/-- **Transfer of the functional calculus**: for `φ` continuous and vanishing at infinity,
`V (φ(A) η) = (φ ∘ m) · V η` a.e. -/
theorem isGood_of_tendsto_cocompact (hm : Measurable m) {φ : ℝ → ℂ} (hφc : Continuous φ)
    (hφ0 : Tendsto φ (cocompact ℝ) (𝓝 0)) : IsGood hA V m φ := by
  set ψ : C(Circ, ℂ) := ⟨circFun φ, continuous_circFun hφc hφ0⟩
  have hψ : ∀ x, ψ (cay x) = φ x := circFun_cay φ
  have hφB : φ ∈ BddMeasurable ℝ :=
    (mem_bddMeasurable).2 ⟨hφc.measurable, ‖ψ‖, fun x => by rw [← hψ x]; exact ψ.norm_coe_le_norm _⟩
  set Alg := StarAlgebra.adjoin ℂ ({circZ} : Set C(Circ, ℂ))
  have hsep : Alg.SeparatesPoints := by
    intro u v huv
    refine ⟨circZ, ⟨circZ, StarAlgebra.subset_adjoin ℂ _ rfl, rfl⟩, ?_⟩
    exact fun h => huv (Subtype.ext h)
  have hcl := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints Alg hsep
  have hmem : ψ ∈ closure (Alg : Set C(Circ, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hcl]; trivial
  refine isGood_of_uniform hm hφB fun ε hε => ?_
  obtain ⟨q, hqA, hq⟩ := Metric.mem_closure_iff.1 hmem ε hε
  refine ⟨fun x => q (cay x), bdd_comp_cay q, isGood_star_adjoin hV hqA, fun x => ?_⟩
  rw [← hψ x, ← dist_eq_norm, dist_comm]
  exact ((ContinuousMap.dist_apply_le_dist (cay x)).trans hq.le)

end transfer2

end Qschubert
