import AcceleratedLogConcave.Root.CoolingExecutable
import AcceleratedLogConcave.Oracle.ExecutableWorkCardinality

/-! Every-tape source work of the literal public tau=1 cooling executable.
The recursive mean supplier pays its own prescribed private geometry. Every
main and active-final child is charged, together with the actual local Gaussian
instructions. Uniform caps also sum over any finite sequence of cooling calls. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingExecutableWork
open Oracle Oracle.TapeLowering Oracle.RecursiveExecutable
open Oracle.NoisyLayer Oracle.RecursiveMeanProgram Oracle.SourceExecutableTables
open Numerics.AffineGraph CoolingExecutable

variable {m nm na nh ns nc d : ℕ} (P : Setup m nm na nh ns nc)

def occurrences : ℕ := (P.layers+1)*nc
def queryBase : ℕ := branching P.layers nm ns m
def workBase : ℕ := fullBranching P.layers nm ns m nh
def childRank (K : ℕ) : ℕ := Precision.precisionRank P.t (K:ℝ)
def localGaussians : ℕ := 3+2*nc+2*P.layers*nc
def queryCap (K : ℕ) : ℕ := occurrences P * queryBase P ^ childRank P K
def workCap (K : ℕ) : ℕ := localGaussians P + 2*occurrences P * workBase P ^ childRank P K

theorem queryBase_le_workBase : queryBase P ≤ workBase P := by
  apply max_le (le_max_left _ _)
  exact (Nat.le_add_left _ _).trans (le_max_right _ _)

/-- Both finite inventories are actual source-constructor inventories. -/
theorem workBase_le_cardinality : workBase P ≤ 4*(P.layers+1)*(nm+ns+1) := by
  have hc := ExecutableWorkCardinality.source_cardinality P.M P.meanNodes P.seeds
  exact ExecutableWorkCardinality.fullBranching_le (layers := P.layers) (ns := ns) hc.1 hc.2.2

theorem meanChild_queries_le (a r σ q : ℝ) :
    syntaxCount .gradient (meanChild P a r σ q).program ≤
      queryBase P ^ Precision.precisionRank P.t q :=
  queries_mean_le P.M P.meanNodes P.anchors P.seeds P.Ds P.δ P.t P.w P.layers
    P.ht P.htq P.privateMesh P.privateNodes a r σ q

theorem meanChild_gaussians_le (a r σ q : ℝ) :
    syntaxCount .gaussian (meanChild P a r σ q).program ≤
      workBase P ^ Precision.precisionRank P.t q :=
  gaussians_meanCore_le P.M P.meanNodes P.anchors P.seeds
    (privateGeometry P.M P.privateMesh) P.privateNodes P.Ds P.δ P.t P.w P.layers
    P.ht P.htq a r σ q

/-- Every original-gradient query, including every fresh final mean supplier. -/
theorem executed_queries_le (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v K) :
    (traceCounts (execute P h v K G x ω).trace).queries ≤ queryCap P K := by
  rw [CoolingExecutable.executed_queries]
  have hm : (∑ i, syntaxCount .gradient (main P h v K i).program) ≤
      nc * queryBase P ^ childRank P K := by
    calc
      _ ≤ ∑ _i : Fin nc, queryBase P ^ childRank P K :=
        Finset.sum_le_sum (fun i _ => meanChild_queries_le P _ _ _ _)
      _ = _ := by simp
  have hf : (∑ i, syntaxCount .gradient (final P h v K i).program) ≤
      nc * queryBase P ^ childRank P K := by
    calc
      _ ≤ ∑ _i : Fin nc, queryBase P ^ childRank P K :=
        Finset.sum_le_sum (fun i _ => meanChild_queries_le P _ _ _ _)
      _ = _ := by simp
  calc
    _ ≤ P.layers*(nc*queryBase P ^ childRank P K)+nc*queryBase P ^ childRank P K :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hm) hf
    _ = queryCap P K := by unfold queryCap occurrences; ring

/-- Exact local Gaussian overhead plus the full main/final recursive inventory. -/
theorem executed_gaussians (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v K) :
    (traceCounts (execute P h v K G x ω).trace).gaussianBlocks =
      localGaussians P + P.layers*(∑ i, syntaxCount .gaussian (main P h v K i).program)+
        ∑ i, syntaxCount .gaussian (final P h v K i).program := by
  rw [execute, run_counts]
  change syntaxCount .gaussian (PrivateSamplingProgram.code (config P h v K)) = _
  rw [PrivateSamplingProgram.syntaxCount_code]
  simp only [ite_true, layerInventory, config, samplingConfig,
    ← gaussianCount_eq_tapeShape, syntaxCounts]
  unfold localGaussians
  ring

theorem executed_gaussians_le (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v K) :
    (traceCounts (execute P h v K G x ω).trace).gaussianBlocks ≤
      localGaussians P + occurrences P * workBase P ^ childRank P K := by
  rw [executed_gaussians]
  have hm : (∑ i, syntaxCount .gaussian (main P h v K i).program) ≤
      nc * workBase P ^ childRank P K := by
    calc
      _ ≤ ∑ _i : Fin nc, workBase P ^ childRank P K :=
        Finset.sum_le_sum (fun i _ => meanChild_gaussians_le P _ _ _ _)
      _ = _ := by simp
  have hf : (∑ i, syntaxCount .gaussian (final P h v K i).program) ≤
      nc * workBase P ^ childRank P K := by
    calc
      _ ≤ ∑ _i : Fin nc, workBase P ^ childRank P K :=
        Finset.sum_le_sum (fun i _ => meanChild_gaussians_le P _ _ _ _)
      _ = _ := by simp
  calc
    _ ≤ localGaussians P + P.layers*(nc*workBase P ^ childRank P K)+
        nc*workBase P ^ childRank P K :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _) hf
    _ = _ := by unfold occurrences; ring

/-- Query and Gaussian work of every actual full-tape execution. -/
theorem executed_full_work_le (h : ℝ) (v : ℝ≥0) (K : ℕ) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v K) :
    (traceCounts (execute P h v K G x ω).trace).queries+
      (traceCounts (execute P h v K G x ω).trace).gaussianBlocks ≤ workCap P K := by
  have hq := (executed_queries_le P h v K G x ω).trans
    (Nat.mul_le_mul_left (occurrences P)
      (pow_le_pow_left' (queryBase_le_workBase P) (childRank P K)))
  have hg := executed_gaussians_le P h v K G x ω
  calc
    _ ≤ occurrences P*workBase P ^ childRank P K +
        (localGaussians P+occurrences P*workBase P ^ childRank P K) := Nat.add_le_add hq hg
    _ = workCap P K := by unfold workCap; ring

/-- Explicit polynomial cardinality base raised only to the actual precision rank. -/
theorem executed_full_work_cardinality_le (h : ℝ) (v : ℝ≥0) (K : ℕ)
    (G : Point d → Point d) (x : Point d) (ω : FullTape P d h v K) :
    (traceCounts (execute P h v K G x ω).trace).queries+
      (traceCounts (execute P h v K G x ω).trace).gaussianBlocks ≤
        localGaussians P + 2*occurrences P *
          (4*(P.layers+1)*(nm+ns+1)) ^ childRank P K :=
  (executed_full_work_le P h v K G x ω).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left (2*occurrences P)
      (pow_le_pow_left' (workBase_le_cardinality P) _)) _)

/-- Entering states may depend on every earlier call: the cap holds pathwise. -/
theorem finite_queries_le (L : ℕ) (h : ℝ) (v : Fin L → ℝ≥0) (K : ℕ)
    (G : Point d → Point d) (x : Fin L → Point d)
    (ω : ∀ i, FullTape P d h (v i) K) :
    (∑ i, (traceCounts (execute P h (v i) K G (x i) (ω i)).trace).queries) ≤ L*queryCap P K := by
  calc
    _ ≤ ∑ _i : Fin L, queryCap P K :=
      Finset.sum_le_sum (fun i _ => executed_queries_le P h (v i) K G (x i) (ω i))
    _ = _ := by simp

theorem finite_full_work_le (L : ℕ) (h : ℝ) (v : Fin L → ℝ≥0) (K : ℕ)
    (G : Point d → Point d) (x : Fin L → Point d)
    (ω : ∀ i, FullTape P d h (v i) K) :
    (∑ i : Fin L, ((traceCounts (execute P h (v i) K G (x i) (ω i)).trace).queries +
      (traceCounts (execute P h (v i) K G (x i) (ω i)).trace).gaussianBlocks)) ≤ L*workCap P K := by
  calc
    _ ≤ ∑ _i : Fin L, workCap P K :=
      Finset.sum_le_sum (fun i _ => executed_full_work_le P h (v i) K G (x i) (ω i))
    _ = _ := by simp

end AcceleratedLogConcave.Root.CoolingExecutableWork
