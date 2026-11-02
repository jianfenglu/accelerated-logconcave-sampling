import AcceleratedLogConcave.Conditional.ScaledJetLaplace

/-! Exact comparison between ordered directional jets and multilinear
Frechet derivatives, to identify actual scaled-jet coordinates with cumulants. -/
noncomputable section
open scoped ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Conditional.JetCalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*}

theorem jet_eq_iteratedFDeriv {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ι → E) (l : List ι) (x : E) :
    jet v l f x = iteratedFDeriv ℝ l.length f x (fun i => v (l.get i)) := by
  induction l generalizing x with
  | nil => simp [jet]
  | cons i l ih =>
    change fderiv ℝ (jet v l f) x (v i) = _
    have he : jet v l f = fun y => iteratedFDeriv ℝ l.length f y
        (fun k => v (l.get k)) := funext ih
    rw [he]
    symm
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ l.length f) x :=
      hf.contDiffAt.differentiableAt_iteratedFDeriv (m := l.length) (by exact_mod_cast ENat.natCast_lt_top l.length)
    have heval := hd.iteratedFDeriv_succ_apply_left'
      (m := fun k => v ((i::l).get k))
    have htail : Fin.tail (fun k : Fin (l.length+1) => v ((i::l).get k)) =
        fun k => v (l.get k) := by funext k; rfl
    change iteratedFDeriv ℝ (l.length+1) f x (fun k => v ((i::l).get k)) = _
    rw [htail] at heval
    exact heval

end AcceleratedLogConcave.Conditional.JetCalculus

namespace AcceleratedLogConcave.Conditional.Appell
open MeasureTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Exact local first log-Laplace derivative; this is used in the output slot
of the lifted actual conditional cumulant, not as a moment bound. -/
theorem fderiv_log_laplace_one_of_exp_norm {μ : Measure E} [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 < r) (hμ : Integrable (fun x : E => Real.exp (r*‖x‖)) μ)
    {θ : E} (hθ : θ ∈ Metric.ball (0 : E) (r/2)) (u : E) :
    fderiv ℝ (fun z => Real.log (laplace μ (fun _ => (1 : ℝ)) z)) θ u =
      (laplace μ (fun _ => (1 : ℝ)) θ)⁻¹ *
        laplace μ (fun z => inner ℝ u z) θ := by
  have hd := hasFDerivAt_laplace_of_exp_norm hr hμ continuous_const (HasGrowth.const (1 : ℝ)) hθ
  have hp := laplace_one_pos_of_exp_norm hr hμ
    (show ‖θ‖ ≤ r/2 from (by simpa using hθ : ‖θ‖ < r/2).le)
  have hl := hd.log hp.ne'
  rw [hl.fderiv]
  change (laplace μ (fun _ => (1 : ℝ)) θ)⁻¹ *
    laplace μ (inserted (fun _ => (1 : ℝ))) θ u = _
  rw [laplace_inserted_apply_of_exp_norm hr hμ continuous_const
    (HasGrowth.const (1 : ℝ)) (by simpa using (Metric.mem_ball.mp hθ).le) u]
  simp only [smul_eq_mul, mul_one]

end AcceleratedLogConcave.Conditional.Appell
