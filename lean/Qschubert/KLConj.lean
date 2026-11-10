import Qschubert.KLFriedrichs2
import Qschubert.KLWeightP
import Qschubert.GLInvariance
import Qschubert.Bridge

/-!
# The general boundary point: conjugate groups

For `p ∈ PGL(2, ℝ)`, `Γ' = pΓp⁻¹`. The map `[z] ↦ [p • z]` is a measure-preserving bijection `M → M'`, so `T u = u ∘ Φ`
is a unitary `L²(M') → L²(M)` with `T(F_{Γ'}) = (F ∘ p)_Γ`.

* `conjU`, `conjU_perioT`, `perio_phi`;
* `negLapMH_conj`, `propCLM_conj`, `LapIterM.conj`: `T` intertwines `-Δ_M`, `U_M` and `Δ_M^N`;
* `perioConv_conj`, `conjU_toLp`;
* `approxErr_general`: for `b = g • ∞`, the error of the statement is the `b = ∞` Dyson integral over `Γ' = g⁻¹Γg` for
  the amplitude `a ∘ g`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Matrix
open scoped ENNReal Pointwise MatrixGroups

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

variable (p : PGL(2, ℝ)) (Γ : Subgroup PGL(2, ℝ))

/-- `pΓp⁻¹`. -/
def conjS : Subgroup PGL(2, ℝ) := Γ.map (MulAut.conj p).toMonoidHom

/-- `γ ↦ pγp⁻¹`. -/
noncomputable def conjE : Γ ≃* conjS p Γ := (MulAut.conj p).subgroupMap Γ

lemma conjE_coe (γ : Γ) : ((conjE p Γ γ : conjS p Γ) : PGL(2, ℝ)) = p * γ * p⁻¹ := rfl

lemma conjE_smul (γ : Γ) (z : ℍ) : conjE p Γ γ • (p • z) = p • (γ • z) := by
  show ((conjE p Γ γ : conjS p Γ) : PGL(2, ℝ)) • (p • z) = p • ((γ : PGL(2, ℝ)) • z)
  rw [conjE_coe, mul_smul, mul_smul, inv_smul_smul]

lemma conjE_inv_smul (γ : Γ) (z : ℍ) : p⁻¹ • (conjE p Γ γ • z) = γ • (p⁻¹ • z) := by
  rw [inv_smul_eq_iff, ← conjE_smul, smul_inv_smul]

instance [ProperlyDiscontinuousSMul Γ ℍ] : ProperlyDiscontinuousSMul (conjS p Γ) ℍ := ⟨fun {K L} hK hL => by
  have hc : Continuous fun z : ℍ => p⁻¹ • z := continuous_const_smul _
  have h := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) (hK.image hc) (hL.image hc)
  refine (h.image (conjE p Γ)).subset fun γ' hγ' => ?_
  obtain ⟨γ, rfl⟩ := (conjE p Γ).surjective γ'
  refine ⟨γ, ?_, rfl⟩
  obtain ⟨y, ⟨k, hk, rfl⟩, hy⟩ := hγ'
  exact ⟨γ • (p⁻¹ • k), ⟨p⁻¹ • k, ⟨k, hk, rfl⟩, rfl⟩, ⟨_, hy, conjE_inv_smul p Γ γ k⟩⟩⟩

instance [Countable Γ] : Countable (conjS p Γ) := (conjE p Γ).surjective.countable

/-- `Φ : M → M'`, `[z] ↦ [p • z]`. -/
noncomputable def surfPhi : Surf Γ → Surf (conjS p Γ) :=
  Quotient.lift (fun z => surfMk (conjS p Γ) (p • z)) (by
    rintro a b ⟨γ, rfl⟩
    show surfMk (conjS p Γ) (p • (γ • b)) = surfMk (conjS p Γ) (p • b)
    rw [← conjE_smul, surfMk_smul])

/-- `Φ⁻¹`. -/
noncomputable def surfPsi : Surf (conjS p Γ) → Surf Γ :=
  Quotient.lift (fun z => surfMk Γ (p⁻¹ • z)) (by
    rintro a b ⟨γ', rfl⟩
    obtain ⟨γ, rfl⟩ := (conjE p Γ).surjective γ'
    show surfMk Γ (p⁻¹ • (conjE p Γ γ • b)) = surfMk Γ (p⁻¹ • b)
    rw [conjE_inv_smul, surfMk_smul])

lemma surfPhi_mk (z : ℍ) : surfPhi p Γ (surfMk Γ z) = surfMk _ (p • z) := rfl
lemma surfPsi_mk (z : ℍ) : surfPsi p Γ (surfMk _ z) = surfMk Γ (p⁻¹ • z) := rfl

lemma surfPsi_phi (x : Surf Γ) : surfPsi p Γ (surfPhi p Γ x) = x := by
  induction x using Quotient.inductionOn with | _ z
  show surfMk Γ (p⁻¹ • p • z) = surfMk Γ z
  rw [inv_smul_smul]

lemma surfPhi_psi (x : Surf (conjS p Γ)) : surfPhi p Γ (surfPsi p Γ x) = x := by
  induction x using Quotient.inductionOn with | _ z
  show surfMk _ (p • p⁻¹ • z) = surfMk _ z
  rw [smul_inv_smul]

lemma measurable_surfPhi : Measurable (surfPhi p Γ) :=
  measurable_from_quotient.2 ((measurable_surfMk _).comp (measurable_const_smul p))

lemma measurable_surfPsi : Measurable (surfPsi p Γ) :=
  measurable_from_quotient.2 ((measurable_surfMk _).comp (measurable_const_smul p⁻¹))

/-- `Φ` as a measurable equivalence. -/
noncomputable def surfE : Surf Γ ≃ᵐ Surf (conjS p Γ) where
  toFun := surfPhi p Γ
  invFun := surfPsi p Γ
  left_inv := surfPsi_phi p Γ
  right_inv := surfPhi_psi p Γ
  measurable_toFun := measurable_surfPhi p Γ
  measurable_invFun := measurable_surfPsi p Γ

variable [ProperlyDiscontinuousSMul Γ ℍ]

/-- `Φ` preserves the measure. -/
theorem mp_surfPhi : MeasurePreserving (surfPhi p Γ) (surfMeasure Γ) (surfMeasure (conjS p Γ)) := by
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  have hmp := measurePreserving_smul p (volume : Measure ℍ)
  have hF' : IsFundamentalDomain (conjS p Γ) ((MulAction.toPerm p : Equiv.Perm ℍ) '' fdSet Γ) volume :=
    hF.image_of_equiv (MulAction.toPerm p)
      (measurePreserving_smul p⁻¹ (volume : Measure ℍ)).quasiMeasurePreserving (conjE p Γ).symm.toEquiv
      (fun γ' z => by
        obtain ⟨γ, rfl⟩ := (conjE p Γ).surjective γ'
        show p • ((conjE p Γ).symm (conjE p Γ γ) • z) = conjE p Γ γ • p • z
        rw [MulEquiv.symm_apply_apply, conjE_smul])
  refine ⟨measurable_surfPhi p Γ, ?_⟩
  rw [surfMeasure_eq Γ hF, surfMeasure_eq (conjS p Γ) hF', Measure.map_map (measurable_surfPhi p Γ) (measurable_surfMk Γ)]
  have hc : surfPhi p Γ ∘ surfMk Γ = surfMk (conjS p Γ) ∘ fun z => p • z := rfl
  have hr := hmp.restrict_image_emb (measurableEmbedding_const_smul p) (fdSet Γ)
  rw [hc, ← Measure.map_map (measurable_surfMk _) (measurable_const_smul p), hr.map_eq]
  rfl

theorem mp_surfPsi : MeasurePreserving (surfPsi p Γ) (surfMeasure (conjS p Γ)) (surfMeasure Γ) :=
  (MeasurePreserving.symm (surfE p Γ) (mp_surfPhi p Γ))

local notation "L2M" => Lp ℂ 2 (surfMeasure Γ)
local notation "L2M'" => Lp ℂ 2 (surfMeasure (conjS p Γ))

noncomputable def conjUL : L2M' →ₗᵢ[ℂ] L2M := Lp.compMeasurePreservingₗᵢ ℂ (surfPhi p Γ) (mp_surfPhi p Γ)
noncomputable def conjUL' : L2M →ₗᵢ[ℂ] L2M' := Lp.compMeasurePreservingₗᵢ ℂ (surfPsi p Γ) (mp_surfPsi p Γ)

lemma conjUL_ae (f : L2M') : ⇑(conjUL p Γ f) =ᵐ[surfMeasure Γ] fun x => f (surfPhi p Γ x) :=
  Lp.coeFn_compMeasurePreserving f _

lemma conjUL'_ae (f : L2M) : ⇑(conjUL' p Γ f) =ᵐ[surfMeasure (conjS p Γ)] fun x => f (surfPsi p Γ x) :=
  Lp.coeFn_compMeasurePreserving f _

lemma conjUL_conjUL' (f : L2M) : conjUL p Γ (conjUL' p Γ f) = f := by
  apply Lp.ext
  have h := (mp_surfPhi p Γ).quasiMeasurePreserving.ae_eq_comp (conjUL'_ae p Γ f)
  filter_upwards [conjUL_ae p Γ (conjUL' p Γ f), h] with x e1 e2
  rw [e1]
  have e3 : (conjUL' p Γ f : Surf (conjS p Γ) → ℂ) (surfPhi p Γ x) = f (surfPsi p Γ (surfPhi p Γ x)) := e2
  rw [e3, surfPsi_phi]

/-- **The unitary `T : L²(M') → L²(M)`.** -/
noncomputable def conjU : L2M' ≃ₗᵢ[ℂ] L2M :=
  LinearIsometryEquiv.ofSurjective (conjUL p Γ) fun f => ⟨conjUL' p Γ f, conjUL_conjUL' p Γ f⟩

lemma conjU_apply (f : L2M') : conjU p Γ f = conjUL p Γ f := rfl

lemma conjU_ae (f : L2M') : ⇑(conjU p Γ f) =ᵐ[surfMeasure Γ] fun x => f (surfPhi p Γ x) := conjUL_ae p Γ f

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- `u_{Γ'} ∘ Φ = (u ∘ p)_Γ`, pointwise. -/
lemma perio_phi (u : ℍ → ℂ) (x : Surf Γ) :
    perio (conjS p Γ) u (surfPhi p Γ x) = perio Γ (fun z => u (p • z)) x := by
  induction x using Quotient.inductionOn with | _ z
  show ∑' γ' : conjS p Γ, u (γ' • p • z) = ∑' γ : Γ, u (p • γ • z)
  rw [← (conjE p Γ).toEquiv.tsum_eq (fun γ' : conjS p Γ => u (γ' • p • z))]
  refine tsum_congr fun γ => ?_
  show u (conjE p Γ γ • p • z) = _
  rw [conjE_smul]

/-- `p • z` on test functions. -/
noncomputable def testP (p : PGL(2, ℝ)) (F : testFn) : testFn := testCompT (pglRep p) F

lemma tfn_testP (F : testFn) (z : ℍ) : tfn (testP p F) z = tfn F (p • z) := by
  show testComp (pglRep p) F z = _
  rw [testComp_coe, pglRep_smul]
  rfl

lemma perioT_congr {F G : testFn} (h : ∀ z, tfn F z = tfn G z) : perioT Γ F = perioT Γ G := by
  apply Lp.ext
  have e : tfn F = tfn G := funext h
  have h1 := perioL2_ae Γ (tfn F) (continuous_tfn F) (hasCompactSupport_tfn F)
  have h2 := perioL2_ae Γ (tfn G) (continuous_tfn G) (hasCompactSupport_tfn G)
  have hp : perio Γ (tfn F) = perio Γ (tfn G) := by rw [e]
  filter_upwards [h1, h2] with x a b
  exact a.trans ((congrFun hp x).trans b.symm)

/-- `T (F_{Γ'}) = (F ∘ p)_Γ`. -/
theorem conjU_perioT (F : testFn) : conjU p Γ (perioT (conjS p Γ) F) = perioT Γ (testP p F) := by
  apply Lp.ext
  have h1 := perioL2_ae (conjS p Γ) (tfn F) (continuous_tfn F) (hasCompactSupport_tfn F)
  have h2 := (mp_surfPhi p Γ).quasiMeasurePreserving.ae_eq_comp h1
  have h3 := perioL2_ae Γ (tfn (testP p F)) (continuous_tfn _) (hasCompactSupport_tfn _)
  filter_upwards [conjU_ae p Γ (perioT (conjS p Γ) F), h2, h3] with x a1 a2 a3
  have a2' : (perioT (conjS p Γ) F : Surf (conjS p Γ) → ℂ) (surfPhi p Γ x) = perio (conjS p Γ) (tfn F) (surfPhi p Γ x) := a2
  have e : (fun z => tfn F (p • z)) = tfn (testP p F) := funext fun z => (tfn_testP p F z).symm
  rw [a1, a2', perio_phi, e]
  exact a3.symm

theorem conjU_symm_perioT (F : testFn) : (conjU p Γ).symm (perioT Γ F) = perioT (conjS p Γ) (testP p⁻¹ F) := by
  apply (conjU p Γ).injective
  rw [LinearIsometryEquiv.apply_symm_apply, conjU_perioT]
  refine perioT_congr Γ fun z => ?_
  rw [tfn_testP, tfn_testP, inv_smul_smul]

lemma lapTest_testP (F : testFn) : lapTest (testP p F) = testP p (lapTest F) := lapTest_testCompT _ F

theorem intertwines_conj : IntertwinesOp (negLapM (conjS p Γ)) (negLapM Γ) (conjU p Γ) where
  mem x hx := by
    obtain ⟨F, hF⟩ := exists_eq_perioT (conjS p Γ) ⟨x, hx⟩
    change perioT (conjS p Γ) F = x at hF
    rw [← hF, conjU_perioT]
    exact perioT_mem_negLapM_domain Γ _
  comm x hx := by
    obtain ⟨F, hF⟩ := exists_eq_perioT (conjS p Γ) x
    have hφ : perioT Γ (testP p F) = conjU p Γ (x : L2M') := by rw [← hF, conjU_perioT]
    rw [negLapM_apply_of_eq Γ ⟨_, hx⟩ (testP p F) hφ, negLapM_apply_of_eq (conjS p Γ) x F hF, map_neg, conjU_perioT,
      lapTest_testP]

theorem intertwines_conj_symm : IntertwinesOp (negLapM Γ) (negLapM (conjS p Γ)) (conjU p Γ).symm where
  mem x hx := by
    obtain ⟨F, hF⟩ := exists_eq_perioT Γ ⟨x, hx⟩
    change perioT Γ F = x at hF
    rw [← hF, conjU_symm_perioT]
    exact perioT_mem_negLapM_domain _ _
  comm x hx := by
    obtain ⟨F, hF⟩ := exists_eq_perioT Γ x
    have hφ : perioT (conjS p Γ) (testP p⁻¹ F) = (conjU p Γ).symm (x : L2M) := by rw [← hF, conjU_symm_perioT]
    rw [negLapM_apply_of_eq (conjS p Γ) ⟨_, hx⟩ (testP p⁻¹ F) hφ, negLapM_apply_of_eq Γ x F hF, map_neg,
      conjU_symm_perioT, lapTest_testP]

/-- **`T` intertwines `-Δ_M`.** -/
theorem negLapMH_conj (v : L2M') (hv : v ∈ (negLapMH (conjS p Γ)).domain) :
    ∃ h : conjU p Γ v ∈ (negLapMH Γ).domain, negLapMH Γ ⟨conjU p Γ v, h⟩ = conjU p Γ (negLapMH (conjS p Γ) ⟨v, hv⟩) :=
  friedrichsExt_U2 (negLapM (conjS p Γ)) (negLapM Γ) (negLapM_hasDenseDomain _) (negLapM_hasDenseDomain Γ)
    (intertwines_conj p Γ) (intertwines_conj_symm p Γ) ⟨v, hv⟩

/-- **`T` intertwines `U_M(t)`.** -/
theorem propCLM_conj (hb t : ℝ) (v : L2M') :
    conjU p Γ (propCLM (conjS p Γ) hb t v) = propCLM Γ hb t (conjU p Γ v) :=
  evol_intertwine (negLapMH_isSelfAdjoint _) (negLapMH_isSelfAdjoint Γ) (conjU p Γ).toContinuousLinearEquiv.toContinuousLinearMap
    (fun v hv => negLapMH_conj p Γ v hv) hb t v

/-- **`T` intertwines `Δ_M^N`.** -/
theorem LapIterM.conj : ∀ (N : ℕ) {u v : L2M'}, LapIterM (conjS p Γ) N u v → LapIterM Γ N (conjU p Γ u) (conjU p Γ v)
  | 0, u, v, h => by
      obtain rfl : u = v := h
      rfl
  | N + 1, u, v, ⟨h, hi⟩ => by
      obtain ⟨h', e⟩ := negLapMH_conj p Γ u h
      refine ⟨h', ?_⟩
      rw [e, ← map_neg]
      exact LapIterM.conj N hi

/-- Convergence of periodizations transports. -/
theorem perioConv_conj {u : ℍ → ℂ} (hu : PerioConv (conjS p Γ) u) : PerioConv Γ (fun z => u (p • z)) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [(measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae hu.1] with z hz
    have h := ((conjE p Γ).toEquiv.summable_iff (f := fun γ' : conjS p Γ => ‖u (γ' • p • z)‖)).2 hz
    refine h.congr fun γ => ?_
    show ‖u (conjE p Γ γ • p • z)‖ = ‖u (p • γ • z)‖
    rw [conjE_smul]
  · have h := hu.2.comp_measurePreserving (mp_surfPhi p Γ)
    refine (memLp_congr_ae (Eventually.of_forall fun x => ?_)).1 h
    show perio (conjS p Γ) u (surfPhi p Γ x) = _
    exact perio_phi p Γ u x

theorem conjU_toLp {u : ℍ → ℂ} (hu : PerioConv (conjS p Γ) u) (hu2 : PerioConv Γ (fun z => u (p • z))) :
    hu2.2.toLp _ = conjU p Γ (hu.2.toLp _) := by
  apply Lp.ext
  have h2 := (mp_surfPhi p Γ).quasiMeasurePreserving.ae_eq_comp hu.2.coeFn_toLp
  filter_upwards [hu2.2.coeFn_toLp, conjU_ae p Γ (hu.2.toLp _), h2] with x a1 a2 a3
  have a3' : (hu.2.toLp _ : Surf (conjS p Γ) → ℂ) (surfPhi p Γ x) = perio (conjS p Γ) u (surfPhi p Γ x) := a3
  rw [a1, a2, a3', perio_phi]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- Orbit sums over `Γ'` and `Γ` have the same supremum when `p` fixes `x₀`. -/
theorem iSup_tsum_conj {x₀ : ℍ} (hp : p • x₀ = x₀) (h : ℝ → ℝ≥0∞) :
    ⨆ z : ℍ, ∑' γ' : conjS p Γ, h (dist x₀ (γ' • z)) = ⨆ z : ℍ, ∑' γ : Γ, h (dist x₀ (γ • z)) := by
  rw [← (MulAction.toPerm p : Equiv.Perm ℍ).iSup_comp]
  refine iSup_congr fun w => ?_
  show ∑' γ' : conjS p Γ, h (dist x₀ (γ' • p • w)) = _
  rw [← (conjE p Γ).toEquiv.tsum_eq (fun γ' : conjS p Γ => h (dist x₀ (γ' • p • w)))]
  refine tsum_congr fun γ => ?_
  show h (dist x₀ (conjE p Γ γ • p • w)) = _
  rw [conjE_smul]
  conv_lhs => rw [← hp]
  rw [dist_smul]

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- `P_{Γ'} = P_Γ` when `p` fixes `x₀`. -/
theorem poincareSup_conj {x₀ : ℍ} (hp : p • x₀ = x₀) (s : ℝ) : poincareSup (conjS p Γ) x₀ s = poincareSup Γ x₀ s :=
  iSup_tsum_conj p Γ hp fun d => ENNReal.ofReal (Real.exp (-(s * d)))

/-! ### The general boundary point -/

lemma initState_eq (g : SL(2, ℝ)) (hb : ℝ) (a : ℍ → ℂ) :
    initState g hb a = fun z => trPh hb 0 (fun w => a (g • w)) (SpecialLinearGroup.toPGL g⁻¹ • z) := by
  funext z
  rw [toPGL_smul, trPh_zero, smul_inv_smul]
  rfl

lemma approxSolB_eq (g : SL(2, ℝ)) (K : ℕ) (hb t : ℝ) (a : ℍ → ℂ) :
    approxSolB g K hb t a = fun z => approxSol K hb t (fun w => a (g • w)) (SpecialLinearGroup.toPGL g⁻¹ • z) := by
  funext z
  rw [toPGL_smul]
  rfl

lemma conjU_toLp' {u f : ℍ → ℂ} (hfun : f = fun z => u (p • z)) (hu : PerioConv (conjS p Γ) u) (hf : PerioConv Γ f) :
    hf.2.toLp _ = conjU p Γ (hu.2.toLp _) := by
  subst hfun
  exact conjU_toLp p Γ hu hf

section general

variable {Γ} [Countable Γ] {g : SL(2, ℝ)} {a : ℍ → ℂ}
  {W : SurfW (conjS (SpecialLinearGroup.toPGL g⁻¹) Γ)} (hf : SmoothH fun w => a (g • w)) {A : L2H'}
  (ha : ⇑A =ᵐ[volume] fun w => a (g • w)) (hA : AllWords A) {Ga : List Bool → L2H'}
  (hGa : ∀ w, W.Chart (Ga w) (wordAct w A))
include hf ha hA hGa

/-- Both periodizations of the statement converge, for every boundary point. -/
theorem perioConv_general (K : ℕ) (hb t : ℝ) :
    PerioConv Γ (initState g hb a) ∧ PerioConv Γ (approxSolB g K hb t a) := by
  obtain ⟨h1, h2⟩ := perioConv_infty hf ha hA hGa K t hb
  rw [initState_eq, approxSolB_eq]
  exact ⟨perioConv_conj _ Γ h1, perioConv_conj _ Γ h2⟩

/-- **The error of the statement for the boundary point `b = g • ∞`**, as the Dyson integral over `g⁻¹Γg`. -/
theorem approxErr_general {hb : ℝ} (hb0 : hb ≠ 0) (K N : ℕ) (t : ℝ) (hv : PerioConv Γ (initState g hb a))
    (hw : PerioConv Γ (approxSolB g K hb t a)) :
    approxErr Γ N hb t hv hw = ‖(Complex.I * (hb : ℂ) / 2) ^ (K + 1)
      • simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) A)‖ₑ := by
  set p := SpecialLinearGroup.toPGL g⁻¹
  obtain ⟨hv', hw'⟩ := perioConv_infty hf ha hA hGa K t hb
  have e1 := conjU_toLp' p Γ (initState_eq g hb a) hv' hv
  have e2 := conjU_toLp' p Γ (approxSolB_eq g K hb t a) hw' hw
  have hC := LapIterM.conj p Γ N (lapIter_infty hf ha hA hGa hb0 K N t hv' hw')
  rw [map_sub, propCLM_conj, ← e1, ← e2] at hC
  rw [approxErr, propM_apply, errNormM_of_lapIter hC, ← ofReal_norm, ← ofReal_norm, LinearIsometryEquiv.norm_map,
    propCLM_eq_evol, norm_evol]

end general

end Qschubert
