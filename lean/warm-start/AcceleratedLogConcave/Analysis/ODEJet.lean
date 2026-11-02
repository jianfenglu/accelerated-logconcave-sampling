import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Recursive state jets are evaluated
only along an already supplied actual trajectory. No new flow is constructed
and no global Lipschitz premise on the coupled state field is used. -/
noncomputable section
open Set
open scoped ContDiff
namespace AcceleratedLogConcave.Analysis.ODEJet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Universal time-derivative expressions for a nonautonomous vector field. -/
def stateJet (U : Set (ℝ × E)) (V : ℝ × E → E) : ℕ → ℝ × E → E
  | 0 => Prod.snd
  | n + 1 => fun p => fderivWithin ℝ (stateJet U V n) U p (1, V p)

theorem contDiffOn_stateJet {U : Set (ℝ × E)} (hU : UniqueDiffOn ℝ U)
    {V : ℝ × E → E} (hV : ContDiffOn ℝ ∞ V U) (n : ℕ) :
    ContDiffOn ℝ ∞ (stateJet U V n) U := by
  induction n with
  | zero => exact contDiff_snd.contDiffOn
  | succ n ih =>
    exact (ih.fderivWithin hU (by simp)).clm_apply (contDiffOn_const.prodMk hV)

/-- The chain rule identifies consecutive fields along the actual curve. -/
theorem hasDerivAt_stateJet_along {U : Set (ℝ × E)} (hU : IsOpen U)
    {V : ℝ × E → E} (hV : ContDiffOn ℝ ∞ V U)
    {X : ℝ → E} {t : ℝ} (hp : (t, X t) ∈ U)
    (hX : HasDerivAt X (V (t, X t)) t) (n : ℕ) :
    HasDerivAt (fun u => stateJet U V n (u, X u))
      (stateJet U V (n + 1) (t, X t)) t := by
  have hd := ((contDiffOn_stateJet hU.uniqueDiffOn hV n).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)
  simpa only [stateJet, fderivWithin_of_isOpen hU hp, Function.comp_def, id_eq] using hh

/-- Exact finite-order inequality used for polynomial-envelope induction.
An order-q derivative of the next state jet only uses previous-jet orders
through q+1 and velocity orders through q. -/
theorem norm_iteratedFDerivWithin_stateJet_succ_le
    {U : Set (ℝ × E)} (hU : UniqueDiffOn ℝ U)
    {V : ℝ × E → E} (hV : ContDiffOn ℝ ∞ V U)
    (n q : ℕ) {p : ℝ × E} (hp : p ∈ U) :
    ‖iteratedFDerivWithin ℝ q (stateJet U V (n + 1)) U p‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ (i + 1) (stateJet U V n) U p‖ *
        ‖iteratedFDerivWithin ℝ (q - i) (fun z => ((1 : ℝ), V z)) U p‖ := by
  have hJ := contDiffOn_stateJet hU hV n
  have hVel : ContDiffOn ℝ ∞ (fun z : ℝ × E => ((1 : ℝ), V z)) U :=
    contDiffOn_const.prodMk hV
  have hh := norm_iteratedFDerivWithin_clm_apply
    (hJ.fderivWithin hU (by simp)) hVel hU hp
    (by simp : (q : ℕ∞ω) ≤ ∞)
  simp_rw [norm_iteratedFDerivWithin_fderivWithin hU hp] at hh
  exact hh

/-- Joint continuity needs only joint continuity of the actual curve family;
it requires no initial-input derivative of that family. -/
theorem continuousOn_stateJet_along
    {A : Type*} [TopologicalSpace A] {U : Set (ℝ × E)}
    (hU : UniqueDiffOn ℝ U) {V : ℝ × E → E}
    (hV : ContDiffOn ℝ ∞ V U) {T : Set (ℝ × A)}
    {X : ℝ × A → E} (hX : ContinuousOn X T)
    (hmap : MapsTo (fun p : ℝ × A => (p.1, X p)) T U) (n : ℕ) :
    ContinuousOn (fun p : ℝ × A => stateJet U V n (p.1, X p)) T :=
  (contDiffOn_stateJet hU hV n).continuousOn.comp
    (continuous_fst.continuousOn.prodMk hX) hmap

end AcceleratedLogConcave.Analysis.ODEJet
