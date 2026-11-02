import AcceleratedLogConcave.Oracle.RecursiveExecutableGaussianWork
import AcceleratedLogConcave.Oracle.RecursiveExecutableShiftBudget

/-! Actual finite geometry controls the complete branching base. The leading
factor two counts both terminal instructions and is explicitly paid. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Oracle.ExecutableWorkCardinality
open Numerics.AffineGraph RecursiveExecutable TapeLowering
variable {m n ns h layers d : ℕ}

theorem source_cardinality (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (seeds : Fin h ≃ Fin m × M.Kernel) :
    m ≤ n ∧ h = m*(Fintype.card (M.backward.Source m)+1) ∧ h ≤ n := by
  have hn : n = Fintype.card M.MeanNode := by simpa using Fintype.card_congr nodes
  have hh : h = m*(Fintype.card (M.backward.Source m)+1) := by
    simpa only [Fintype.card_fin, Fintype.card_prod, MeanGeometry.Kernel, Fintype.card_option] using Fintype.card_congr seeds
  rw [M.card_meanNode] at hn
  refine ⟨by omega, hh, ?_⟩
  rw [Nat.mul_add, Nat.mul_one] at hh
  omega

theorem fullBranching_le (hm : m ≤ n) (hh : h ≤ n) :
    fullBranching layers n ns m h ≤ 4*(layers+1)*(n+ns+1) := by
  unfold fullBranching gaussianLocal
  apply max_le
  · have hp : 0 < 4*(layers+1)*(n+ns+1) := by positivity
    omega
  · nlinarith

theorem fullBranching_le_source (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (seeds : Fin h ≃ Fin m × M.Kernel) (layers ns : ℕ) :
    (fullBranching layers n ns m h:ℝ) ≤ sourceShiftBase layers (n+ns) := by
  have hc := source_cardinality M nodes seeds
  have h1 := fullBranching_le (layers := layers) (ns := ns) hc.1 hc.2.2
  have h2 : 4*(layers+1)*(n+ns+1) ≤ 100*(layers+2)*(n+ns+1) :=
    Nat.mul_le_mul_right _ (by omega)
  have hb := h1.trans h2
  unfold sourceShiftBase
  exact_mod_cast hb

theorem sourceShiftBase_ge_two (layers inventory : ℕ) : 2 ≤ sourceShiftBase layers inventory := by
  unfold sourceShiftBase
  have hl : 0 ≤ (layers:ℝ) := Nat.cast_nonneg _
  have hi : 0 ≤ (inventory:ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hl hi]

/-- The two terminal instructions consume the additional available power. -/
theorem absorb_leading_two {b rank bound : ℕ} {D : ℝ} (hD : 2 ≤ D)
    (hb : (b:ℝ) ≤ D) (hrank : rank+1 ≤ bound) :
    ((2*b^rank:ℕ):ℝ) ≤ D^bound := by
  have hD0 : 0 ≤ D := by linarith
  calc
    _ = 2*(b:ℝ)^rank := by push_cast; rfl
    _ ≤ D*D^rank := mul_le_mul hD (pow_le_pow_left₀ (Nat.cast_nonneg _) hb _)
      (pow_nonneg (Nat.cast_nonneg _) _) hD0
    _ = D^(rank+1) := (pow_succ' D rank).symm
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hrank

/-- Exact every-tape terminal work: one gradient query and one Gaussian block. -/
theorem terminal_work_exact (scale r σ : ℝ) (oracle : Point d → Point d)
    (input : Inputs d (terminal scale r σ).size)
    (tape : Tape d (terminal scale r σ).program) :
    let counts := traceCounts (run (terminal scale r σ).program oracle input Env.empty tape).trace
    counts.queries = 1 ∧ counts.gaussianBlocks = 1 ∧ counts.queries+counts.gaussianBlocks = 2 := by
  dsimp only
  rw [run_counts]
  have ht : syntaxCounts (RecursiveExecutable.terminal scale r σ).program = ⟨1,1,0⟩ :=
    terminalMeanProgram_counts _
  rw [ht]
  norm_num
end AcceleratedLogConcave.Oracle.ExecutableWorkCardinality
