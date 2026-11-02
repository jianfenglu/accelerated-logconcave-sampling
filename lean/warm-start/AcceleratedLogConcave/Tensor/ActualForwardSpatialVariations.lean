import AcceleratedLogConcave.Tensor.ActualCoefficientAssembly
import AcceleratedLogConcave.Tensor.ActualCutComparison
import AcceleratedLogConcave.Tensor.RankTwoCuts

/-! Literal arbitrary-start forward flow, with its
spatial variations obtained directly from the original zeroth-order ODE.
No inverse-map jet bound, forward regularity oracle, or reversed-flow assertion
is used. Finite-dimensional packing is only linear calculus, never an HS bound. -/
noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped ContDiff Topology Classical
namespace AcceleratedLogConcave.Tensor.ForwardFlow
open Conditional ActualCoefficient Conditional.Transport.SpatialFlow
open AcceleratedLogConcave.Analysis.SpatialVariation
open AcceleratedLogConcave.Analysis.SpatialPartition
open OutputLift
variable {D : ℕ}

/-- rho is the actual fixed initial time; s is the running target time. -/
def forwardY (d : PositiveVarianceFlowData (Space D)) (ρ : Icc (0:ℝ) d.b)
    (s : ℝ) : Space D → Space D :=
  fun y => convexProbabilityFlow d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0
    (by norm_num) d.hb1 ρ y s

/-- This fixes the first time coordinate of the existing two-time representative. -/
theorem exists_smooth_forward_representative
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (y : Space D) :
    ∃ C : ℝ × Space D → Space D, ContDiff ℝ ∞ C ∧
      ∀ s ∈ Icc 0 d.b, ∀ z ∈ ball y 1, C (s,z) = forwardY d ρ s z := by
  obtain ⟨S,hS,he⟩ := Conditional.Transport.exists_smooth_convexProbabilityFlow_extension
    d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 hsmall y
  refine ⟨fun p => S (((ρ:ℝ),p.1),p.2),
    hS.comp ((contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd),?_⟩
  intro s hs z hz
  exact he ρ ⟨s,hs⟩ z hz

theorem contDiff_forwardY (d : PositiveVarianceFlowData (Space D))
    (hsmall : d.r^2*d.ell ≤ 1/2) (ρ : Icc (0:ℝ) d.b)
    {s : ℝ} (hs : s ∈ Icc 0 d.b) : ContDiff ℝ ∞ (forwardY d ρ s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  obtain ⟨C,hC,he⟩ := exists_smooth_forward_representative d hsmall ρ y
  have h : ContDiff ℝ ∞ (fun z : Space D => C (s,z)) :=
    hC.comp (contDiff_const.prodMk contDiff_id)
  apply h.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ)<1)] with z hz
  exact (he s hs z hz).symm

theorem forwardY_hasDerivWithinAt (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) (y : Space D) {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    HasDerivWithinAt (fun u => forwardY d ρ u y)
      (probabilityVelocity d.F d.x d.r s (forwardY d ρ s y)) (Icc 0 d.b) s :=
  convexProbabilityFlow_deriv d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0
    (by norm_num) d.hb1 ρ y hs

/-- All derivative orders, still in fixed initial-point directions. -/
theorem forward_iteratedFDeriv_variation
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (v : Fin n → Space D) (y : Space D)
    {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    HasDerivWithinAt (fun u => iteratedFDeriv ℝ n (forwardY d ρ u) y v)
      (iteratedFDeriv ℝ n
        ((probabilityVelocity d.F d.x d.r s) ∘ forwardY d ρ s) y v)
      (Icc 0 d.b) s := by
  obtain ⟨C,hC,he⟩ := exists_smooth_forward_representative d hsmall ρ y
  have h := along_variation_of_local_representative d.hb0 hC y he
    (fun t ht z _ => forwardY_hasDerivWithinAt d ρ z ht) (List.ofFn v) hs
  have hY := contDiff_forwardY d hsmall ρ hs
  have hV := contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x
    (r := d.r) (by linarith [hs.1]) (hs.2.trans_lt d.hb1)
  have heq := along_ofFn_eq_iteratedFDeriv (hV.comp hY) n v y
  dsimp only [Function.comp_def] at heq
  rw [heq] at h
  exact h.congr_of_mem (fun t ht =>
    (along_ofFn_eq_iteratedFDeriv (contDiff_forwardY d hsmall ρ ht) n v y).symm) hs

abbrev forwardJetCoeff (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (y : Space D) (s : ℝ) :=
  vectorCoeff (iteratedFDeriv ℝ n (forwardY d ρ s) y)

abbrev forwardRHSCoeff (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (y : Space D) (s : ℝ) :=
  vectorCoeff (iteratedFDeriv ℝ n
    ((probabilityVelocity d.F d.x d.r s) ∘ forwardY d ρ s) y)

abbrev forwardForcingCoeff (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 0 < n) (y : Space D) (s : ℝ) :=
  vectorCoeff (spatialForcing (probabilityVelocity d.F d.x d.r s) (forwardY d ρ s) y n hn)

abbrev forwardTopDerivative (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) (y : Space D) (s : ℝ) :=
  fderiv ℝ (probabilityVelocity d.F d.x d.r s) (forwardY d ρ s y)

theorem forward_coefficient_variation
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (y : Space D)
    {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    HasDerivWithinAt (forwardJetCoeff d ρ n y)
      (forwardRHSCoeff d ρ n y s) (Icc 0 d.b) s := by
  have hcoord (a : Fin n ⊕ Unit → Fin D) :=
    (innerSL ℝ (basis D (a (.inr ())))).hasFDerivAt.comp_hasDerivWithinAt s
      (forward_iteratedFDeriv_variation d hsmall ρ n
        (fun i => basis D (a (.inl i))) y hs)
  exact (packCLM _).hasFDerivAt.comp_hasDerivWithinAt s
    (hasDerivWithinAt_pi.mpr hcoord)

theorem forwardRHS_separated
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 0 < n) (y : Space D)
    {s : ℝ} (hs : s ∈ Icc 0 d.b) :
    forwardRHSCoeff d ρ n y s =
      outputAction (.inr ()) (derivativeMatrix (forwardTopDerivative d ρ y s))
        (forwardJetCoeff d ρ n y s) + forwardForcingCoeff d ρ n hn y s := by
  have he := iteratedFDeriv_comp_separated (x := y)
    (contDiff_probabilityVelocity_spatial d.hF d.hlo d.hhi d.x (r := d.r)
      (by linarith [hs.1]) (hs.2.trans_lt d.hb1)).contDiffAt
    (contDiff_forwardY d hsmall ρ hs).contDiffAt n hn
  change vectorCoeff (iteratedFDeriv ℝ n _ y) = _
  rw [he,vectorCoeff_add,← outputAction_vectorCoeff]

/-- Both cut orientations use the exact output action, not a full-HS estimate. -/
theorem forward_unfolded_variation
    (d : PositiveVarianceFlowData (Space D)) (hsmall : d.r^2*d.ell ≤ 1/2)
    (ρ : Icc (0:ℝ) d.b) (n : ℕ) (hn : 0 < n) (y : Space D)
    (S : Finset (Fin n ⊕ Unit)) :
    (∀ s ∈ Icc 0 d.b, HasDerivWithinAt
      (fun u => splitOperatorEquiv D S (forwardJetCoeff d ρ n y u))
      (splitOperatorEquiv D S (forwardRHSCoeff d ρ n y s)) (Icc 0 d.b) s) ∧
    (∀ s ∈ Icc 0 d.b, splitNorm D S (forwardRHSCoeff d ρ n y s) ≤
      ‖forwardTopDerivative d ρ y s‖*splitNorm D S (forwardJetCoeff d ρ n y s) +
        splitNorm D S (forwardForcingCoeff d ρ n hn y s)) := by
  constructor
  · intro s hs
    exact (FixedCut.unfoldCLM S).hasFDerivAt.comp_hasDerivWithinAt s
      (forward_coefficient_variation d hsmall ρ n y hs)
  · intro s hs
    rw [forwardRHS_separated d hsmall ρ n hn y hs]
    exact (splitNorm_add_le D S _ _).trans (add_le_add
      (outputAction_splitNorm_le S (.inr ()) (forwardTopDerivative d ρ y s)
        (forwardJetCoeff d ρ n y s)) le_rfl)

@[simp] theorem forwardY_initial (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) : forwardY d ρ ρ = id := by
  funext y
  exact convexProbabilityFlow_initial d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0
    (by norm_num) d.hb1 ρ y

/-- Literal endpoint identification, paying the orientation explicitly. -/
theorem forwardY_terminal (d : PositiveVarianceFlowData (Space D))
    (ρ : Icc (0:ℝ) d.b) : forwardY d ρ d.b =
      forwardProbabilityTransport d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0 d.hb1 ρ := by
  funext y
  change _ = convexProbabilityFlow d.hF d.hell d.hlo d.hhi d.x d.hr d.hb0
    (by norm_num) d.hb1 (projIcc 0 d.b d.hb0 (ρ:ℝ)) y d.b
  rw [projIcc_of_mem d.hb0 ρ.property]
  rfl

end AcceleratedLogConcave.Tensor.ForwardFlow
