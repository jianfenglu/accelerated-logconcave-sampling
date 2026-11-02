import AcceleratedLogConcave.Analysis.ODEJet

/-! Material derivatives of a smooth observable along an already constructed
actual curve. Unlike stateJet, the observable may have a different codomain. -/
noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
namespace AcceleratedLogConcave.Analysis.ODEJet
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]

def observableJet (U : Set (ℝ × E)) (V : ℝ × E → E) (f : ℝ × E → A) :
    ℕ → ℝ × E → A
  | 0 => f
  | n+1 => fun p => fderivWithin ℝ (observableJet U V f n) U p (1, V p)

theorem contDiffOn_observableJet {U : Set (ℝ × E)} (hU : UniqueDiffOn ℝ U)
    {V : ℝ × E → E} (hV : ContDiffOn ℝ ∞ V U)
    {f : ℝ × E → A} (hf : ContDiffOn ℝ ∞ f U) (n : ℕ) :
    ContDiffOn ℝ ∞ (observableJet U V f n) U := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact (ih.fderivWithin hU (by simp)).clm_apply (contDiffOn_const.prodMk hV)

theorem hasDerivAt_observableJet_along {U : Set (ℝ × E)} (hU : IsOpen U)
    {V : ℝ × E → E} (hV : ContDiffOn ℝ ∞ V U)
    {f : ℝ × E → A} (hf : ContDiffOn ℝ ∞ f U)
    {X : ℝ → E} {t : ℝ} (hp : (t, X t) ∈ U)
    (hX : HasDerivAt X (V (t, X t)) t) (n : ℕ) :
    HasDerivAt (fun u => observableJet U V f n (u, X u))
      (observableJet U V f (n+1) (t, X t)) t := by
  have hd := ((contDiffOn_observableJet hU.uniqueDiffOn hV hf n).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)
  simpa only [observableJet, fderivWithin_of_isOpen hU hp, Function.comp_def, id_eq] using hh

end AcceleratedLogConcave.Analysis.ODEJet
