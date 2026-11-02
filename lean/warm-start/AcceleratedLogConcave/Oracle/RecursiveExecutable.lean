import AcceleratedLogConcave.Oracle.SourceMeanExecutable
import AcceleratedLogConcave.Oracle.SamplingExecutable
import AcceleratedLogConcave.Oracle.TerminalMeanShift

/-! The actual finite precision recursion. Every main, private-sampling and
active-final child is selected here, rather than supplied by a correctness
certificate. Sampling is finite syntax containing smaller mean calls only. -/
noncomputable section
set_option maxRecDepth 10000
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph TapeLowering Precision
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
  (Ds δ t w : ℝ) (ht : 0 < t) (htq : t ≤ 1/4) (layers : ℕ)

def terminal (scale r σ : ℝ) : ExecutableData where
  size := 3
  program := terminalMeanProgram [⟨.mean,.setup,0,0,0⟩]
  coefficient := TerminalMeanShift.coefficients scale r σ
  shift := fun _ => -1

/-- Bottom-up source construction: all program matrices and tape shifts are
computed from the smaller constructed children. No center or tape affects shape. -/
def meanCore (ht : 0 < t) (htq : t ≤ 1/4) (scale r σ q : ℝ) : ExecutableData := by
  classical
  exact if _hq : q ≤ 1/2 then terminal scale r σ else
    let main : Fin n → ExecutableData := fun i =>
      meanCore ht htq scale (M.radius r (nodes i))
        (RecursiveMeanPublicTable.mainWidth n r M.R Ds
          (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4)
    let final : Fin m → ExecutableData := fun _ =>
      meanCore ht htq scale (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)
    let smain : Fin ns → ExecutableData := fun i =>
      meanCore ht htq scale (S.radius r (snodes i))
        (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4)
    let sfinal : Fin ns → ExecutableData := fun i =>
      meanCore ht htq scale (S.radius r (snodes i))
        (SourceExecutableTables.samplingFinalWidth S r) (q-1/4)
    let sampling := SamplingExecutable.build S snodes r Ds smain sfinal layers
    SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w main final sampling layers
      (SamplingExecutable.weights S snodes r Ds smain sfinal layers
        (-2*M.R/backwardEnd M.R))
termination_by precisionRank t q
decreasing_by
  all_goals
    apply Nat.lt_of_succ_le
    apply precisionRank_drop ht (lt_of_not_ge _hq)
    first | exact le_rfl | linarith

/-- Exact terminal source code and public original-gradient scale. -/
theorem mean_terminal (scale r σ q : ℝ) (hq : q ≤ 1/2) :
    meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q =
      terminal scale r σ := by
  rw [meanCore,dite_eq_left hq]

/-- The actual terminal program obeys the full query/trace shift. -/
theorem terminal_queryShift (scale r σ : ℝ) (hr : 0 < r) :
    ChildAbsorption.QueryShift (terminal scale r σ).program
      (terminal scale r σ).enumeration (terminal scale r σ).coefficient r
      (terminal scale r σ).shiftVector :=
  TerminalMeanShift.queryShift_canonical _ scale r σ hr

/-- The private helper has the prescribed same R and tau=R/b*, rather than
an independent sampling geometry chosen by a caller. -/
def privateGeometry (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R))) :
    SamplingGeometry m where
  R := M.R
  R_pos := M.R_pos
  R_le_half := M.R_le_half
  τ := M.R/backwardEnd M.R
  R_le_τ := by
    apply (le_div_iff₀ M.backwardEnd_pos).mpr
    exact mul_le_of_le_one_right M.R_pos.le M.backwardEnd_lt_one.le
  τ_le_one := by
    clear ht htq
    apply (div_le_one₀ M.backwardEnd_pos).mpr
    have hs : (backwardEnd M.R)^2 = 1-M.R^2 := by
      apply Real.sq_sqrt
      nlinarith [M.R_le_half,M.R_pos]
    have hb := M.backwardEnd_pos
    nlinarith [M.R_le_half,M.R_pos]
  mesh := mesh

/-- Source-specialized recursion; the private helper is constructed internally. -/
def mean (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (snodes : Fin ns ≃ mesh.Source m) (scale r σ q : ℝ) : ExecutableData :=
  meanCore M nodes anchors seeds (privateGeometry M mesh) snodes Ds δ t w layers
    ht htq scale r σ q

/-- Global synchronous layer count prescribed by the source schedule. -/
def sourceLayers (Csch : ℝ) (K : ℕ) : ℕ := Nat.ceil (Csch*(K+2))

end AcceleratedLogConcave.Oracle.RecursiveExecutable
