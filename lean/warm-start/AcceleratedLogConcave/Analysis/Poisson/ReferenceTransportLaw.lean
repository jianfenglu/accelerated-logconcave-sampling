import AcceleratedLogConcave.Analysis.Poisson.ReferenceTransportIdentity
import AcceleratedLogConcave.Analysis.Poisson.CompactTestMeasure
import AcceleratedLogConcave.Analysis.Poisson.Pullback

/-! Actual law transport from a classical density continuity equation. The
density is ENNReal-valued in `withDensity`; no pushforward identity is assumed. -/
noncomputable section
open MeasureTheory Set Function
open scoped Topology NNReal ENNReal
namespace AcceleratedLogConcave.Analysis.Poisson
open OAI.LogConcaveSampling.GlobalODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Integration against the actual nonnegative density, with the ENNReal convention. -/
theorem integral_ofReal_density (ρ : E → ℝ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (φ : E → ℝ) :
    (∫ x, φ x ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) =
      ∫ x, ρ x * φ x := by
  rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hpos _), smul_eq_mul]

/-- The constructed complete ODE flow preserves the actual endpoint reference laws.
The assumptions are regularity and the pointwise density continuity equation;
transport itself is proved by compact C1 tests. -/
theorem measurePreserving_flow_of_density_continuity
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
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (ρ a x)))
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal (ρ b x)))
    (hpos_a : ∀ x, 0 ≤ ρ a x) (hpos_b : ∀ x, 0 ≤ ρ b x) :
    MeasurePreserving (flowHomeomorph hL hv ⟨a, le_rfl, hab.le⟩ ⟨b, hab.le, le_rfl⟩) μ ν := by
  let T := flowHomeomorph hL hv ⟨a, le_rfl, hab.le⟩ ⟨b, hab.le, le_rfl⟩
  refine ⟨T.continuous.measurable, ?_⟩
  apply measure_eq_of_compact_contDiff
  intro φ hφ hφK
  rw [integral_map T.continuous.measurable.aemeasurable hφ.continuous.aestronglyMeasurable]
  have hρa : Continuous (ρ a) := hρ.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨⟨le_rfl, hab.le⟩, mem_univ x⟩)
  have hρb : Continuous (ρ b) := hρ.comp_continuous
    (continuous_const.prodMk continuous_id) (fun x => ⟨⟨hab.le, le_rfl⟩, mem_univ x⟩)
  rw [hμ, hν, integral_ofReal_density (ρ a) hρa hpos_a,
    integral_ofReal_density (ρ b) hρb hpos_b]
  exact (density_transport_compact_test hab hv hL hD hvd ρ ρt hρ hρt hdρ hρsp hPDE φ hφ hφK).symm

/-- One constructed flow transports the whole density family on the chosen interval,
including the initial endpoint. -/
theorem measurePreserving_flow_family_of_density_continuity
    {a b : ℝ} (hab : a ≤ b) {v : ℝ → E → E}
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
    (μ : ℝ → Measure E) [∀ t, IsFiniteMeasure (μ t)]
    (hμ : ∀ t ∈ Icc a b, μ t = volume.withDensity (fun x => ENNReal.ofReal (ρ t x)))
    (hpos : ∀ t ∈ Icc a b, ∀ x, 0 ≤ ρ t x) (t : Icc a b) :
    MeasurePreserving (flowHomeomorph hL hv ⟨a, le_rfl, hab⟩ t) (μ a) (μ t) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  rcases eq_or_lt_of_le t.2.1 with he | ht
  · have heq : (flowHomeomorph hL hv ⟨a, le_rfl, hab⟩ t : E → E) = id := by
      funext x
      change flow hL hv ⟨a, le_rfl, hab⟩ x t = x
      rw [← he]
      exact flow_initial hL hv ⟨a, le_rfl, hab⟩ x
    rw [heq, ← he]
    exact MeasurePreserving.id (μ a)
  · have hsub : Icc a (t : ℝ) ⊆ Icc a b := fun s hs => ⟨hs.1, hs.2.trans t.2.2⟩
    have hsubo : Ioo a (t : ℝ) ⊆ Ioo a b := fun s hs => ⟨hs.1, hs.2.trans_le t.2.2⟩
    have h := measurePreserving_flow_of_density_continuity ht hv
      (fun s hs => hL s (hsub hs)) hD hvd ρ ρt
      (hρ.mono (fun p hp => ⟨hsub hp.1, hp.2⟩))
      (hρt.mono (fun p hp => ⟨hsubo hp.1, hp.2⟩))
      (fun s hs => hdρ s (hsubo hs)) (fun s hs => hρsp s (hsubo hs))
      (fun s hs => hPDE s (hsubo hs)) (hμ a ha) (hμ t t.2)
      (hpos a ha) (hpos t t.2)
    have heq : (flowHomeomorph (fun s hs => hL s (hsub hs)) hv
        ⟨a, le_rfl, ht.le⟩ ⟨t, ht.le, le_rfl⟩ : E → E) =
        flowHomeomorph hL hv ⟨a, le_rfl, hab⟩ t := by
      funext x
      exact flow_eq_on_subinterval hv hL hsub ⟨a, le_rfl, ht.le⟩ ⟨t, ht.le, le_rfl⟩ x
    rwa [heq] at h

end AcceleratedLogConcave.Analysis.Poisson
