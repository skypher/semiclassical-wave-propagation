import Qschubert.KLSurf3
import Qschubert.KLDD

/-!
# The Dyson expansion on the surface (`cor:surf-dyson`)

`vS hb s` is the surface object `𝒱_s` as a linear map on `L²(ℍ)`: on a vector `v` with chart `G = ω v` it equals
`surfV hb s G` (`vS_apply`). Off the charted vectors it is an arbitrary linear extension, and it is only ever evaluated
on charted vectors. For `a` with all words in `L²_ω`:
`𝒱_0 a - 𝒱_t a^{(K)}(t) = c^{K+1} ∫_{Σ_{K+1}(t)} 𝒱_{s₁} Δ(s₁)⋯Δ(s_{K+1}) a ds` (`surf_dyson`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ENNReal Pointwise MatrixGroups

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

namespace SurfW

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ)

variable {W}

lemma Chart.unique {G G' v : L2H'} (h : W.Chart G v) (h' : W.Chart G' v) : G = G' := by
  apply Lp.ext
  filter_upwards [h, h'] with z a b
  rw [a, b]

lemma chart_zero : W.Chart (0 : L2H') 0 := by
  show ⇑(0 : L2H') =ᵐ[volume] _
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz
  rw [hz]; simp

variable (W)

/-- The vectors with a chart. -/
def chartSub : Submodule ℂ L2H' where
  carrier := {v | ∃ G, W.Chart G v}
  add_mem' := fun ⟨G₁, h₁⟩ ⟨G₂, h₂⟩ => ⟨G₁ + G₂, h₁.add h₂⟩
  zero_mem' := ⟨0, chart_zero⟩
  smul_mem' := fun c _ ⟨G, h⟩ => ⟨c • G, h.smul c⟩

noncomputable def chartOf (v : W.chartSub) : L2H' := v.2.choose

lemma chart_chartOf (v : W.chartSub) : W.Chart (W.chartOf v) v := v.2.choose_spec

noncomputable def chartL : W.chartSub →ₗ[ℂ] L2H' where
  toFun := W.chartOf
  map_add' x y := ((W.chart_chartOf (x + y)).unique ((W.chart_chartOf x).add (W.chart_chartOf y)))
  map_smul' c x := ((W.chart_chartOf (c • x)).unique ((W.chart_chartOf x).smul c))

/-- `𝒱_s` as a linear map. -/
noncomputable def vS (hb s : ℝ) : L2H' →ₗ[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  (LinearMap.exists_extend ((W.surfV hb s).toLinearMap ∘ₗ W.chartL)).choose

/-- On a vector with chart `G`, `vS` is `surfV` at `G`. -/
theorem vS_apply (hb s : ℝ) {G v : L2H'} (h : W.Chart G v) : W.vS hb s v = W.surfV hb s G := by
  have hs := (LinearMap.exists_extend ((W.surfV hb s).toLinearMap ∘ₗ W.chartL)).choose_spec
  have e := LinearMap.congr_fun hs (⟨v, ⟨G, h⟩⟩ : W.chartSub)
  have e2 : W.chartOf (⟨v, ⟨G, h⟩⟩ : W.chartSub) = G := (W.chart_chartOf ⟨v, ⟨G, h⟩⟩).unique h
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at e
  rw [show W.vS hb s v = _ from e]
  show W.surfV hb s (W.chartOf _) = _
  rw [e2]

/-- `s ↦ 𝒱_s F(s)` is continuous. -/
lemma continuous_surfV_comp {hb : ℝ} {F : ℝ → L2H'} (hF : Continuous F) : Continuous fun s => W.surfV hb s (F s) := by
  have hL : Continuous fun s => W.surfL hb s (F s) := W.perioW.continuous.comp (W.continuous_TW_comp hb hF)
  have hU : Continuous fun s => propCLM Γ hb (-s) (W.surfL hb s (F s)) :=
    continuous_evol_comp (negLapMH_isSelfAdjoint Γ) continuous_neg hL
  have hE : Continuous fun s : ℝ => Complex.exp (-(Complex.I * ((s / (2 * hb) : ℝ) : ℂ))) := by fun_prop
  exact hE.smul hU

/-- `Σ c_i G_{w_i}`. -/
noncomputable def chartP (Ga : List Bool → L2H') (P : WP) : L2H' := (P.map fun t => t.1 • Ga t.2).sum

lemma chartP_cons (Ga : List Bool → L2H') (t : ℂ × List Bool) (P : WP) :
    chartP Ga (t :: P) = t.1 • Ga t.2 + chartP Ga P := by
  simp [chartP]

lemma continuous_chartP (Ga : List Bool → L2H') {R : TP} (hR : Cont R) : Continuous fun s => chartP Ga (atT R s) := by
  induction R with
  | nil => exact continuous_const
  | cons r R ih =>
    have e : (fun s => chartP Ga (atT (r :: R) s)) = fun s => r.1 s • Ga r.2 + chartP Ga (atT R s) := by
      funext s; exact chartP_cons Ga (r.1 s, r.2) (atT R s)
    rw [e]
    exact ((hR r (by simp)).smul continuous_const).add (ih fun q hq => hR q (by simp [hq]))

lemma hasDerivAt_chartP_intTP (Ga : List Bool → L2H') {R : TP} (hR : Cont R) (s : ℝ) :
    HasDerivAt (fun t => chartP Ga (atT (intTP R) t)) (chartP Ga (atT R s)) s := by
  induction R with
  | nil => exact hasDerivAt_const s _
  | cons r R ih =>
    have e : (fun t => chartP Ga (atT (intTP (r :: R)) t))
        = fun t => (∫ x in (0 : ℝ)..t, r.1 x) • Ga r.2 + chartP Ga (atT (intTP R) t) := by
      funext t; exact chartP_cons Ga ((∫ x in (0 : ℝ)..t, r.1 x), r.2) (atT (intTP R) t)
    have e' : chartP Ga (atT (r :: R) s) = r.1 s • Ga r.2 + chartP Ga (atT R s) :=
      chartP_cons Ga (r.1 s, r.2) (atT R s)
    rw [e, e']
    have hc := hR r (by simp)
    have h1 : HasDerivAt (fun t => ∫ x in (0 : ℝ)..t, r.1 x) (r.1 s) s :=
      intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    exact (h1.smul_const _).add (ih fun q hq => hR q (by simp [hq]))

lemma chartP_intTP_zero (Ga : List Bool → L2H') (R : TP) : chartP Ga (atT (intTP R) 0) = 0 := by
  induction R with
  | nil => rfl
  | cons r R ih =>
    have e : chartP Ga (atT (intTP (r :: R)) 0)
        = (∫ x in (0 : ℝ)..0, r.1 x) • Ga r.2 + chartP Ga (atT (intTP R) 0) :=
      chartP_cons Ga ((∫ x in (0 : ℝ)..0, r.1 x), r.2) (atT (intTP R) 0)
    rw [e, ih, intervalIntegral.integral_same, zero_smul, add_zero]

/-- The letters `X`, `Y` as word polynomials. -/
def pZ (z : Bool) : WP := [(1, [z])]

section dyson

variable {W} {a : L2H'} (hA : AllWords a) {Ga : List Bool → L2H'} (hGa : ∀ w, W.Chart (Ga w) (wordAct w a))

include hGa in
lemma chart_chartP (P : WP) : W.Chart (chartP Ga P) (polyAct P a) := by
  induction P with
  | nil => exact chart_zero
  | cons t P ih =>
    rw [chartP_cons, polyAct_cons]
    exact ((hGa t.2).smul t.1).add ih

include hA

/-- A letter on `P a` is the word polynomial `z·P`. -/
lemma domZ_polyAct (z : Bool) (P : WP) :
    domZ z ⟨polyAct P a, mem_polyAct hA P⟩ = polyAct (mulP (pZ z) P) a := by
  rw [← polyAct_mulP hA]
  have h : wordAct [] (polyAct P a) ∈ negLapH.domain := mem_polyAct hA P
  rw [pZ, polyAct_cons, polyAct_nil, add_zero, one_smul, wordAct_cons z [] h]
  rfl

include hGa in
/-- Polynomials of `a` lie in the class `𝒟_ω`. -/
lemma surfIn_poly (P : WP) :
    W.SurfIn ⟨polyAct P a, mem_polyAct hA P⟩ (chartP Ga P) (chartP Ga (mulP (pZ true) P)) (chartP Ga (mulP (pZ false) P))
      (chartP Ga (mulP (pZ true) (mulP (pZ true) P))) (chartP Ga (mulP (pZ false) (mulP (pZ false) P))) := by
  have eX : domX ⟨polyAct P a, mem_polyAct hA P⟩ = polyAct (mulP (pZ true) P) a := domZ_polyAct hA true P
  have eY : domY ⟨polyAct P a, mem_polyAct hA P⟩ = polyAct (mulP (pZ false) P) a := domZ_polyAct hA false P
  have hX : domX ⟨polyAct P a, mem_polyAct hA P⟩ ∈ negLapH.domain := eX ▸ mem_polyAct hA _
  have hY : domY ⟨polyAct P a, mem_polyAct hA P⟩ ∈ negLapH.domain := eY ▸ mem_polyAct hA _
  have eXX : domX ⟨domX ⟨polyAct P a, mem_polyAct hA P⟩, hX⟩ = polyAct (mulP (pZ true) (mulP (pZ true) P)) a := by
    rw [show (⟨domX ⟨polyAct P a, mem_polyAct hA P⟩, hX⟩ : negLapH.domain)
      = ⟨polyAct (mulP (pZ true) P) a, mem_polyAct hA _⟩ from Subtype.ext eX]
    exact domZ_polyAct hA true _
  have eYY : domY ⟨domY ⟨polyAct P a, mem_polyAct hA P⟩, hY⟩ = polyAct (mulP (pZ false) (mulP (pZ false) P)) a := by
    rw [show (⟨domY ⟨polyAct P a, mem_polyAct hA P⟩, hY⟩ : negLapH.domain)
      = ⟨polyAct (mulP (pZ false) P) a, mem_polyAct hA _⟩ from Subtype.ext eY]
    exact domZ_polyAct hA false _
  exact ⟨hX, hY, chart_chartP hGa P, eX ▸ chart_chartP hGa _, eY ▸ chart_chartP hGa _,
    eXX ▸ chart_chartP hGa _, eYY ▸ chart_chartP hGa _⟩

/-- `Δ(s) u` as a word polynomial. -/
lemma vec_del (s : ℝ) (P : WP) (hX : domX ⟨polyAct P a, mem_polyAct hA P⟩ ∈ negLapH.domain)
    (hY : domY ⟨polyAct P a, mem_polyAct hA P⟩ ∈ negLapH.domain) :
    ((Real.exp (-2 * s) : ℝ) : ℂ) • domX ⟨domX ⟨polyAct P a, mem_polyAct hA P⟩, hX⟩
        + domY ⟨domY ⟨polyAct P a, mem_polyAct hA P⟩, hY⟩ - domY ⟨polyAct P a, mem_polyAct hA P⟩
      = polyAct (deltaP s) (polyAct P a) := by
  set u := polyAct P a with hu
  have hUA : AllWords u := allWords_polyAct hA P
  have hud : wordAct [] u ∈ negLapH.domain := mem_polyAct hA P
  have hXm : wordAct [true] u ∈ negLapH.domain := AllWords.mem hUA [true]
  have hYm : wordAct [false] u ∈ negLapH.domain := AllWords.mem hUA [false]
  have eX : wordAct [true] u = domX ⟨u, mem_polyAct hA P⟩ := by
    rw [wordAct_cons true [] hud]; simp only [domZ, ite_true]; rfl
  have eY : wordAct [false] u = domY ⟨u, mem_polyAct hA P⟩ := by
    rw [wordAct_cons false [] hud]; simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  have eXX : wordAct [true, true] u = domX ⟨domX ⟨u, mem_polyAct hA P⟩, hX⟩ := by
    rw [wordAct_cons true [true] hXm]; simp only [domZ, ite_true]; congr 1; exact Subtype.ext eX
  have eYY : wordAct [false, false] u = domY ⟨domY ⟨u, mem_polyAct hA P⟩, hY⟩ := by
    rw [wordAct_cons false [false] hYm]; simp only [domZ, Bool.false_eq_true, ite_false]; congr 1; exact Subtype.ext eY
  rw [deltaP, polyAct_cons, polyAct_cons, polyAct_cons, polyAct_nil, eXX, eYY, eY]
  have hneg : ∀ x : L2H', (-1 : ℂ) • x = -x := fun x => neg_one_smul ℂ x
  show _ = ((Real.exp (-2 * s) : ℝ) : ℂ) • _ + ((1 : ℂ) • _ + ((-1 : ℂ) • _ + 0))
  rw [hneg, one_smul, add_zero]
  abel

include hGa

/-- `Δ(s)` in the chart. -/
lemma gDel_chartP (s : ℝ) (P : WP) :
    gDel s (chartP Ga (mulP (pZ false) P)) (chartP Ga (mulP (pZ true) (mulP (pZ true) P)))
      (chartP Ga (mulP (pZ false) (mulP (pZ false) P))) = chartP Ga (mulP (deltaP s) P) := by
  have h := surfIn_poly hA hGa P
  refine (h.chart_del s).unique ?_
  have hc := chart_chartP hGa (mulP (deltaP s) P)
  rw [vec_del hA s P h.hX h.hY, polyAct_mulP hA]
  exact hc

variable {hb : ℝ} (hb0 : hb ≠ 0)
include hb0

/-- The moving-input Duhamel formula on `M`, for Dyson-type polynomials. -/
theorem surf_path {Q : TP} (hQ : Cont Q) (t : ℝ) :
    W.vS hb t (polyAct (atT (intTP Q) t) a)
      = ∫ s in (0 : ℝ)..t, (W.vS hb s (polyAct (atT Q s) a)
          - (Complex.I * (hb : ℂ) / 2) • W.vS hb s (polyAct (deltaP s) (polyAct (atT (intTP Q) s) a))) := by
  have hR := cont_intTP hQ
  set R := intTP Q
  have hmulc : ∀ (A : WP), Continuous fun s => chartP Ga (mulP A (atT R s)) := fun A => by
    have e : (fun s => chartP Ga (mulP A (atT R s))) = fun s => chartP Ga (atT (mulTP (constTP A) R) s) := by
      funext s; rw [atT_mulTP, atT_constTP]
    rw [e]
    exact continuous_chartP Ga (cont_mulTP (cont_constTP _) hR)
  have hmulc2 : ∀ (A B : WP), Continuous fun s => chartP Ga (mulP A (mulP B (atT R s))) := fun A B => by
    have e : (fun s => chartP Ga (mulP A (mulP B (atT R s))))
        = fun s => chartP Ga (atT (mulTP (constTP A) (mulTP (constTP B) R)) s) := by
      funext s; rw [atT_mulTP, atT_constTP, atT_mulTP, atT_constTP]
    rw [e]
    exact continuous_chartP Ga (cont_mulTP (cont_constTP _) (cont_mulTP (cont_constTP _) hR))
  have h := surf_duhamel hb0 (g := fun s => ⟨polyAct (atT R s) a, mem_polyAct hA _⟩)
    (G := fun s => chartP Ga (atT R s)) (G' := fun s => chartP Ga (atT Q s))
    (GX := fun s => chartP Ga (mulP (pZ true) (atT R s))) (GY := fun s => chartP Ga (mulP (pZ false) (atT R s)))
    (GXX := fun s => chartP Ga (mulP (pZ true) (mulP (pZ true) (atT R s))))
    (GYY := fun s => chartP Ga (mulP (pZ false) (mulP (pZ false) (atT R s))))
    (fun s => surfIn_poly hA hGa _) (fun s => hasDerivAt_chartP_intTP Ga hQ s) (continuous_chartP Ga hQ)
    (hmulc _) (hmulc2 _ _) (hmulc2 _ _) 0 t
  have e0 : chartP Ga (atT R 0) = 0 := chartP_intTP_zero Ga Q
  simp only [e0, map_zero, sub_zero] at h
  rw [W.vS_apply hb t (chart_chartP hGa _), h]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show W.surfV hb s _ = _
  rw [gDel_chartP hA hGa, map_sub, map_smul, W.vS_apply hb s (chart_chartP hGa _), polyAct_mulP hA,
    W.vS_apply hb s (chart_chartP hGa _)]

/-- `𝒱_t a - 𝒱_0 a = -c J₀(t)`. -/
theorem surf_zero (t : ℝ) :
    W.vS hb t a - W.vS hb 0 a
      = -(Complex.I * (hb : ℂ) / 2) • ∫ s in (0 : ℝ)..t, W.vS hb s (polyAct (deltaP s) (xK a 0 s)) := by
  have hmulc : ∀ (A : WP), Continuous fun _ : ℝ => chartP Ga (mulP A oneP) := fun A => continuous_const
  have hc0 : Continuous fun _ : ℝ => (0 : L2H') := continuous_const
  have h := surf_duhamel hb0 (g := fun _ => ⟨polyAct oneP a, mem_polyAct hA _⟩)
    (G := fun _ => chartP Ga oneP) (G' := fun _ => 0)
    (GX := fun _ => chartP Ga (mulP (pZ true) oneP)) (GY := fun _ => chartP Ga (mulP (pZ false) oneP))
    (GXX := fun _ => chartP Ga (mulP (pZ true) (mulP (pZ true) oneP)))
    (GYY := fun _ => chartP Ga (mulP (pZ false) (mulP (pZ false) oneP)))
    (fun s => surfIn_poly hA hGa _) (fun s => hasDerivAt_const s _) hc0
    continuous_const continuous_const continuous_const 0 t
  have eC : W.Chart (chartP Ga oneP) a := by
    have := chart_chartP hGa oneP
    rwa [polyAct_oneP] at this
  rw [← W.vS_apply hb t eC, ← W.vS_apply hb 0 eC] at h
  rw [h, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show W.surfV hb s _ = _
  have e1 := W.vS_apply hb s (chart_chartP hGa (mulP (deltaP s) oneP))
  rw [gDel_chartP hA hGa, zero_sub, map_neg, map_smul, ← e1, ← polyAct_mulP hA, polyAct_oneP, xK_zero]
  exact (_root_.neg_smul _ _).symm

/-- The Dyson integrand is continuous. -/
lemma continuous_surf_integrand (k : ℕ) :
    Continuous fun s => W.vS hb s (polyAct (deltaP s) (xK a k s)) := by
  have e : (fun s => W.vS hb s (polyAct (deltaP s) (xK a k s)))
      = fun s => W.surfV hb s (chartP Ga (atT (mulTP deltaT (dysT k)) s)) := by
    funext s
    rw [poly_delta_xK hA, W.vS_apply hb s (chart_chartP hGa _)]
  rw [e]
  exact W.continuous_surfV_comp (continuous_chartP Ga (cont_mulTP cont_deltaT (cont_dysT k)))

/-- `J_k` on `M`. -/
noncomputable def jS (W : SurfW Γ) (hb : ℝ) (a : L2H') (k : ℕ) (t : ℝ) : Lp ℂ 2 (surfMeasure Γ) :=
  ∫ s in (0 : ℝ)..t, W.vS hb s (polyAct (deltaP s) (xK a k s))

/-- `𝒱_t P_{k+1}(t) a = J_k(t) - c J_{k+1}(t)`. -/
theorem surf_succ (k : ℕ) (t : ℝ) :
    W.vS hb t (xK a (k + 1) t) = jS W hb a k t - (Complex.I * (hb : ℂ) / 2) • jS W hb a (k + 1) t := by
  have h := surf_path hA hGa hb0 (cont_mulTP cont_deltaT (cont_dysT k)) t
  have c1 := continuous_surf_integrand hA hGa hb0 k
  have c2 := continuous_surf_integrand hA hGa hb0 (k + 1)
  have e1 : ∀ s, W.vS hb s (polyAct (atT (mulTP deltaT (dysT k)) s) a)
      = W.vS hb s (polyAct (deltaP s) (xK a k s)) := fun s => by rw [poly_delta_xK hA]
  show W.vS hb t (polyAct (atT (intTP (mulTP deltaT (dysT k))) t) a) = _
  rw [h]
  simp_rw [e1]
  set c : ℂ := Complex.I * (hb : ℂ) / 2
  have c3 : Continuous fun s => c • W.vS hb s (polyAct (deltaP s) (xK a (k + 1) s)) := c2.const_smul c
  show ∫ s in (0 : ℝ)..t, (W.vS hb s (polyAct (deltaP s) (xK a k s))
    - c • W.vS hb s (polyAct (deltaP s) (xK a (k + 1) s))) = _
  rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c3.intervalIntegrable _ _),
    intervalIntegral.integral_smul]
  rfl

/-- **`cor:surf-dyson`, integrated form**: `𝒱_0 a - 𝒱_t Σ_{k≤K} c^k P_k(t) a = c^{K+1} J_K(t)`. -/
theorem surf_dyson_J (K : ℕ) (t : ℝ) :
    W.vS hb 0 a - W.vS hb t (∑ k ∈ Finset.range (K + 1), (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t)
      = (Complex.I * (hb : ℂ) / 2) ^ (K + 1) • jS W hb a K t := by
  set c : ℂ := Complex.I * (hb : ℂ) / 2
  have hL : ∀ (K : ℕ), W.vS hb t (∑ k ∈ Finset.range (K + 1), c ^ k • xK a k t)
      = ∑ k ∈ Finset.range (K + 1), c ^ k • W.vS hb t (xK a k t) := fun K => by
    simp only [map_sum, map_smul]
  rw [hL]
  induction K with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_smul, xK_zero, pow_one]
    have h := surf_zero hA hGa hb0 t
    have h' : W.vS hb t a = W.vS hb 0 a + -(c • jS W hb a 0 t) := by
      refine (eq_add_of_sub_eq' h).trans ?_
      congr 1
      exact _root_.neg_smul _ _
    rw [h']
    abel
  | succ K ih =>
    rw [Finset.sum_range_succ, surf_succ hA hGa hb0, ← sub_sub, ih, smul_sub, smul_smul, pow_succ c (K + 1)]
    abel

/-- `J_K(t)` as a simplex integral. -/
theorem jS_eq_simplex (K : ℕ) (t : ℝ) :
    jS W hb a K t = simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (deltaProd ss) a) := by
  show _ = ∫ s in (0 : ℝ)..t, simplexInt K s
    (fun l => W.vS hb ((s :: l).headD 0) (polyAct (deltaProd (s :: l)) a))
  unfold jS
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hf : (fun l => W.vS hb ((s :: l).headD 0) (polyAct (deltaProd (s :: l)) a))
      = fun l => W.vS hb s (polyAct (deltaP s) (polyAct (deltaProd l) a)) := by
    funext l
    rw [polyAct_deltaProd_cons hA]
    rfl
  show W.vS hb s (polyAct (deltaP s) (xK a K s)) = _
  simp only [hf]
  rw [simplex_poly hA]

/-- **`cor:surf-dyson`**: the Dyson expansion on `M`. -/
theorem surf_dyson (K : ℕ) (t : ℝ) :
    W.vS hb 0 a - W.vS hb t (∑ k ∈ Finset.range (K + 1), (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t)
      = (Complex.I * (hb : ℂ) / 2) ^ (K + 1)
        • simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (deltaProd ss) a) := by
  rw [surf_dyson_J hA hGa hb0, jS_eq_simplex hA hGa hb0]

end dyson

end SurfW

end Qschubert
