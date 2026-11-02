import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransport
import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportFlow

/-!
# Transport of compact tests from the actual density continuity equation

The backward test is constructed from the ODE flow. Its material derivative
vanishes by the chain rule, and the density continuity equation then proves
conservation of its expectation. Conservation is a conclusion, not a premise.
-/

noncomputable section
open MeasureTheory InnerProductSpace Set Filter Function
open scoped RealInnerProductSpace Topology NNReal

namespace AcceleratedLogConcave.Analysis.Poisson
open OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A classical density continuity equation transports every compact C1 test
along the constructed globally Lipschitz spatial flow. -/
theorem density_transport_compact_test
    {a b : ℝ} (hab : a < b) {v : ℝ → E → E}
    (hv : Continuous (uncurry v)) {C : ℝ≥0}
    (hL : ∀ t ∈ Icc a b, LipschitzWith C (v t))
    {D : ℝ → E → E →L[ℝ] E} (hD : Continuous (uncurry D))
    (hvd : ∀ t x, HasFDerivAt (v t) (D t x) x)
    (ρ ρt : ℝ → E → ℝ)
    (hρ : ContinuousOn (uncurry ρ) (Icc a b ×ˢ (univ : Set E)))
    (hρt : ContinuousOn (uncurry ρt) (Ioo a b ×ˢ (univ : Set E)))
    (hdρ : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => ρ s x) (ρt t x) t)
    (hρsp : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (ρ t))
    (hPDE : ∀ t ∈ Ioo a b, ∀ x,
      ρt t x + fluxDivergence (fun y => ρ t y • v t y) x = 0)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ) :
    (∫ x, ρ b x * φ x) =
      ∫ x, ρ a x * φ (flow hL hv ⟨a, le_rfl, hab.le⟩ x b) := by
  let T : Icc a b := ⟨b, hab.le, le_rfl⟩
  let ψ := backwardTest hab.le hv hL T φ
  let η := fun t x => ψ (t, x)
  let ηt := fun t x => fderiv ℝ ψ (t, x) (1, 0)
  have hψ : Continuous ψ := backwardTest_continuous hab.le hv hL T hφ.continuous
  have hψ₁ (p : ℝ × E) (hp : p.1 ∈ Ioo a b) : ContDiffAt ℝ 1 ψ p :=
    backwardTest_contDiffAt_one hab.le hv hL hD hvd T hφ p hp
  have hψon : ContDiffOn ℝ 1 ψ (Ioo a b ×ˢ (univ : Set E)) :=
    fun p hp => (hψ₁ p hp.1).contDiffWithinAt
  have hηt : ContinuousOn (uncurry ηt) (Ioo a b ×ˢ (univ : Set E)) :=
    (hψon.continuousOn_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ) le_rfl).clm_apply
      continuousOn_const
  have hdη (t : ℝ) (ht : t ∈ Ioo a b) (x : E) :
      HasDerivAt (fun s => η s x) (ηt t x) t := by
    have hp : HasFDerivAt ψ (fderiv ℝ ψ (t, x)) (t, x) :=
      ((hψ₁ (t, x) ht).differentiableAt (by norm_num)).hasFDerivAt
    exact hp.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hηsp (t : ℝ) (ht : t ∈ Ioo a b) : ContDiff ℝ 1 (η t) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hψ₁ (t, x) ht).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hvsp (t : ℝ) : ContDiff ℝ 1 (v t) :=
    contDiff_one_iff_hasFDerivAt.mpr ⟨D t,
      hD.comp (continuous_const.prodMk continuous_id), hvd t⟩
  obtain ⟨S, hS, hzero⟩ := backwardTest_common_compact_support hab.le hv hL T hφK
  let Q := fun t => ∫ x, ρ t x * η t x
  have hQc : ContinuousOn Q (Icc a b) :=
    continuousOn_integral_of_common_compact_support (fun t x => ρ t x * η t x)
      (hρ.mul hψ.continuousOn) S hS (fun t _ x hx => by
        change ρ t x * backwardTest hab.le hv hL T φ (t, x) = 0
        rw [hzero t x hx, mul_zero])
  have hQd (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt Q 0 t := by
    have hd := hasDerivAt_density_test_integral ρ ρt η ηt (v t) ht
      (hρ.mono (fun p hp => ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩)) hρt
      hψ.continuousOn hηt hdρ hdη (hρsp t ht) (hvsp t) (hηsp t ht)
      S hS (fun s _ x hx => hzero s x hx) (hPDE t ht)
    have hz (x : E) : ηt t x + fderiv ℝ (η t) x (v t x) = 0 := by
      have hdsp := ((hψ₁ (t, x) ht).differentiableAt (by norm_num)).hasFDerivAt.comp x
        ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id x))
      change ηt t x + fderiv ℝ (ψ ∘ Prod.mk t) x (v t x) = 0
      rw [hdsp.fderiv]
      change fderiv ℝ ψ (t, x) (1, 0) + fderiv ℝ ψ (t, x) (0, v t x) = 0
      rw [← map_add]
      simpa only [Prod.mk_add_mk, add_zero, zero_add] using
        backwardTest_material_zero hab.le hv hL hD hvd T hφ.differentiable_one (t, x) ht
    simpa only [hz, mul_zero, integral_zero] using hd
  obtain ⟨t, ht, he⟩ := exists_deriv_eq_slope Q hab hQc
    (fun t ht => (hQd t ht).differentiableAt.differentiableWithinAt)
  rw [(hQd t ht).deriv] at he
  have heq : Q b = Q a :=
    sub_eq_zero.mp ((div_eq_zero_iff).mp he.symm |>.resolve_right (sub_ne_zero.mpr hab.ne'))
  have hb : Q b = ∫ x, ρ b x * φ x := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [Q, η, ψ]
    rw [backwardTest_eq, projIcc_of_mem _ (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)]
    rw [flow_initial]
  have ha : Q a = ∫ x, ρ a x * φ (flow hL hv ⟨a, le_rfl, hab.le⟩ x b) := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [Q, η, ψ]
    rw [backwardTest_eq, projIcc_of_mem _ (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)]
  exact hb.symm.trans (heq.trans ha)

end AcceleratedLogConcave.Analysis.Poisson
