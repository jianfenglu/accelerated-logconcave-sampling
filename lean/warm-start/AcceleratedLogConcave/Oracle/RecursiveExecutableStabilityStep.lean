import AcceleratedLogConcave.Oracle.FixedTapeStabilityGrowth
import AcceleratedLogConcave.Oracle.RecursiveExecutable
import AcceleratedLogConcave.Oracle.SourceMeanExecutableStability
import AcceleratedLogConcave.Oracle.SamplingExecutableStability

/-! One actual precision-recursion step under four explicit child IH families.
The smaller radii, widths and precision parameters are the literal constructor
arguments. No fuel induction, reachable-call invariant or uniform constant is proved. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph FixedTapeStability TapeLowering
open scoped BigOperators NNReal

variable {d m n a h ms ns : ℕ}
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds δ t w : ℝ) (N : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)
    (scale r σ q : ℝ)

local notation "E" => meanCore M nodes anchors seeds S snodes Ds δ t w N ht htq scale
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

/-- At and below the cutoff, the actual normalized terminal oracle pays the bound. -/
theorem meanCore_childStable_terminal (hq : q ≤ 1/2)
    (G : Point d → Point d) (L : ℝ≥0)
    (hG : LipschitzWith L (fun x => scale • G (scale • x))) :
    ChildStable (E r σ q).program (E r σ q).coefficient G L := by
  rw [mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq N scale r σ q hq]
  exact terminal_childStable _ scale r σ G L hG

/-- The actual one-step mean constructor, including its computed private sampler.
κm bounds mean main/final children; κs bounds sampling main/final children.
The row mass is explicit and need not satisfy a contraction bound. -/
theorem meanCore_childStable_step (hq : 1/2 < q)
    (G : Point d → Point d) (κm κs A : ℝ)
    (hm : 0 < m) (hms : 0 < ms) (hr : 0 ≤ r)
    (hκm : 0 ≤ κm) (hκs : 0 ≤ κs) (hA : 0 ≤ A) (hpsi : M.psi ≤ M.R^4)
    (hmain : ∀ i, ChildStable (mainChild i).program (mainChild i).coefficient G κm)
    (hfinal : ∀ i, ChildStable (finalChild i).program (finalChild i).coefficient G κm)
    (hsmain : ∀ i, ChildStable (samplingMain i).program (samplingMain i).coefficient G κs)
    (hsfinal : ∀ i, ChildStable (samplingFinal i).program (samplingFinal i).coefficient G κs)
    (hrow : ∀ i : M.MeanNode, ∑ j, |M.matrix r σ i j| ≤ A) :
    ChildStable (E r σ q).program (E r σ q).coefficient G
      (meanGrowth N κm κs r (backwardEnd M.R) A) := by
  have hs : ChildStable
      (SamplingExecutable.build S snodes r Ds samplingMain samplingFinal N).program
      (SamplingExecutable.build S snodes r Ds samplingMain samplingFinal N).coefficient G
      (samplingGrowth N κs r) :=
    FixedTapeSampling.build_childStable S snodes r Ds samplingMain samplingFinal N G κs
      hms hr hκs hsmain hsfinal
  have hb := SourceMeanStability.build_childStable M nodes anchors seeds r σ Ds δ t w
    mainChild finalChild (SamplingExecutable.build S snodes r Ds samplingMain samplingFinal N) N
    (SamplingExecutable.weights S snodes r Ds samplingMain samplingFinal N
      (-2*M.R/backwardEnd M.R)) G κm (samplingGrowth N κs r) A hm hr hκm
    (samplingGrowth_nonneg N hκs hr) hA hpsi hmain hfinal hs hrow
  rw [meanCore,dite_eq_right (not_le.mpr hq)]
  exact hb

/-- A concrete execution comparison retains the same entering P and complete raw tape. -/
theorem meanCore_sub_le_step (hq : 1/2 < q)
    (G : Point d → Point d) (κm κs A : ℝ)
    (hm : 0 < m) (hms : 0 < ms) (hr : 0 ≤ r)
    (hκm : 0 ≤ κm) (hκs : 0 ≤ κs) (hA : 0 ≤ A) (hpsi : M.psi ≤ M.R^4)
    (hmain : ∀ i, ChildStable (mainChild i).program (mainChild i).coefficient G κm)
    (hfinal : ∀ i, ChildStable (finalChild i).program (finalChild i).coefficient G κm)
    (hsmain : ∀ i, ChildStable (samplingMain i).program (samplingMain i).coefficient G κs)
    (hsfinal : ∀ i, ChildStable (samplingFinal i).program (samplingFinal i).coefficient G κs)
    (hrow : ∀ i : M.MeanNode, ∑ j, |M.matrix r σ i j| ≤ A)
    (P x y : Point d) (tape : Tape d (E r σ q).program) :
    ‖RetainedMeanFinalBatch.childPoint (run (E r σ q).program G
        ⟨(E r σ q).coefficient,x,P⟩ Env.empty tape) -
      RetainedMeanFinalBatch.childPoint (run (E r σ q).program G
        ⟨(E r σ q).coefficient,y,P⟩ Env.empty tape)‖ ≤
      meanGrowth N κm κs r (backwardEnd M.R) A * ‖x-y‖ := by
  exact childStable_tape _ _ G _
    (meanCore_childStable_step M nodes anchors seeds S snodes Ds δ t w N ht htq scale r σ q
      hq G κm κs A hm hms hr hκm hκs hA hpsi hmain hfinal hsmain hsfinal hrow) P x y tape

end AcceleratedLogConcave.Oracle.RecursiveExecutable
