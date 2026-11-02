import AcceleratedLogConcave.Oracle.SamplingZeroLayerStability
import AcceleratedLogConcave.Oracle.SourceMeanZeroLayerStability
import AcceleratedLogConcave.Oracle.RecursiveExecutableStabilityStep

/-! Actual zero-layer nonterminal recursion has only the two final child families.
The unused main families remain in the executable carrier, with no stability or row premise. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph FixedTapeStability TapeLowering
open scoped BigOperators NNReal

variable {d m n a h ms ns : ℕ}
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds δ t w : ℝ) (ht : 0 < t) (htq : t ≤ 1/4)
    (scale r σ q : ℝ)

local notation "E" => meanCore M nodes anchors seeds S snodes Ds δ t w 0 ht htq scale
local notation "mainChild" => (fun i : Fin n =>
  E (M.radius r (nodes i))
    (RecursiveMeanPublicTable.mainWidth n r M.R Ds
      (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4))
local notation "finalChild" => (fun _ : Fin m =>
  E (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t))
local notation "samplingMain" => (fun i : Fin ns =>
  E (S.radius r (snodes i)) (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4))
local notation "samplingFinal" => (fun i : Fin ns =>
  E (S.radius r (snodes i)) (SourceExecutableTables.samplingFinalWidth S r) (q-1/4))

theorem meanCore_childStable_zero (hq : 1/2 < q)
    (G : Point d → Point d) (κm κs : ℝ)
    (hm : 0 < m) (hms : 0 < ms) (hr : 0 ≤ r)
    (hκm : 0 ≤ κm) (hκs : 0 ≤ κs) (hpsi : M.psi ≤ M.R^4)
    (hfinal : ∀ i, ChildStable (finalChild i).program (finalChild i).coefficient G κm)
    (hsfinal : ∀ i, ChildStable (samplingFinal i).program (samplingFinal i).coefficient G κs) :
    ChildStable (E r σ q).program (E r σ q).coefficient G
      (κm*(1+r*(backwardEnd M.R)^2*(κs*r))) := by
  have hs := FixedTapeSampling.build_zero_childStable S snodes r Ds samplingMain samplingFinal
    G κs hms hr hκs hsfinal
  have hb := SourceMeanStability.build_zero_childStable M nodes anchors seeds r σ Ds δ t w
    mainChild finalChild (SamplingExecutable.build S snodes r Ds samplingMain samplingFinal 0)
    (SamplingExecutable.weights S snodes r Ds samplingMain samplingFinal 0
      (-2*M.R/backwardEnd M.R)) G κm (κs*r) hm hr hκm
    (mul_nonneg hκs hr) hpsi hfinal hs
  rw [meanCore,dite_eq_right (not_le.mpr hq)]
  exact hb

/-- The row parameter is arbitrary and disappears at zero layers. -/
theorem meanCore_childStable_zero_growth (hq : 1/2 < q)
    (G : Point d → Point d) (κm κs A : ℝ)
    (hm : 0 < m) (hms : 0 < ms) (hr : 0 ≤ r)
    (hκm : 0 ≤ κm) (hκs : 0 ≤ κs) (hpsi : M.psi ≤ M.R^4)
    (hfinal : ∀ i, ChildStable (finalChild i).program (finalChild i).coefficient G κm)
    (hsfinal : ∀ i, ChildStable (samplingFinal i).program (samplingFinal i).coefficient G κs) :
    ChildStable (E r σ q).program (E r σ q).coefficient G
      (meanGrowth 0 κm κs r (backwardEnd M.R) A) := by
  simpa only [meanGrowth_zero_layers] using
    meanCore_childStable_zero M nodes anchors seeds S snodes Ds δ t w ht htq scale r σ q
      hq G κm κs hm hms hr hκm hκs hpsi hfinal hsfinal

theorem meanCore_sub_le_zero (hq : 1/2 < q)
    (G : Point d → Point d) (κm κs : ℝ)
    (hm : 0 < m) (hms : 0 < ms) (hr : 0 ≤ r)
    (hκm : 0 ≤ κm) (hκs : 0 ≤ κs) (hpsi : M.psi ≤ M.R^4)
    (hfinal : ∀ i, ChildStable (finalChild i).program (finalChild i).coefficient G κm)
    (hsfinal : ∀ i, ChildStable (samplingFinal i).program (samplingFinal i).coefficient G κs)
    (P x y : Point d) (tape : Tape d (E r σ q).program) :
    ‖RetainedMeanFinalBatch.childPoint (run (E r σ q).program G
        ⟨(E r σ q).coefficient,x,P⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run (E r σ q).program G
        ⟨(E r σ q).coefficient,y,P⟩ Env.empty tape)‖ ≤
      (κm*(1+r*(backwardEnd M.R)^2*(κs*r))) * ‖x-y‖ := by
  exact childStable_tape _ _ G _
    (meanCore_childStable_zero M nodes anchors seeds S snodes Ds δ t w ht htq scale r σ q
      hq G κm κs hm hms hr hκm hκs hpsi hfinal hsfinal) P x y tape

end AcceleratedLogConcave.Oracle.RecursiveExecutable
