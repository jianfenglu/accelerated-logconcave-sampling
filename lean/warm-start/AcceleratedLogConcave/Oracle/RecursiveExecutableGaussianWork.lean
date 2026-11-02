import AcceleratedLogConcave.Oracle.RecursiveExecutableWork

/-! Actual Gaussian-block inventory and deterministic query-plus-Gaussian work
of the complete precision program. No executed occurrence receives a discount. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph TapeLowering Precision NoisyLayer RecursiveMeanProgram
open AffineLowering RecursiveMeanContinuation RetainedMeanFinalBatch
open scoped BigOperators

private theorem gaussians_sourceMean (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (main : Fin n → ExecutableData) (final : Fin m → ExecutableData)
    (sampling : ExecutableData) (layers : ℕ) :
    syntaxCount .gaussian (SourceMeanExecutable.program M nodes anchors seeds main final sampling layers) =
      syntaxCount .gaussian sampling.program + (m+1+h+n+2*layers*n) +
        layers*(∑ i, syntaxCount .gaussian (main i).program) +
          ∑ i, syntaxCount .gaussian (final i).program := by
  have hb : syntaxCount .gaussian
      (SourceMeanExecutable.body (a := a) (h := h) M nodes main final sampling layers) =
      n + (layers*layerInventory .gaussian (fun i => (main i).size) (fun i => (main i).program) +
        ∑ i, (tapeShape (final i).program).gaussianBlocks) := by
    unfold SourceMeanExecutable.body NonterminalMeanBlock.code
    rw [syntaxCount_initialize]
    simp only [ite_true]
    congr 1
    apply syntaxCount_iterateThen
    intro Δ old direct saved
    simp [paidCorrection,syntaxCount,syntaxCount_designatedChild,syntaxCount_lower,
      RetainedMeanCorrection.syntaxCount_code,Fin.sum_ofFn]
  rw [SourceMeanExecutable.program,syntaxCount,syntaxCount]
  norm_num only [instructionCount,Instr.eventKind]
  rw [SourceMeanExecutable.incoming,MeanExecutablePrefix.syntaxCount_code]
  simp only [ite_true,hb,layerInventory,← gaussianCount_eq_tapeShape,syntaxCounts]
  simp only [reduceCtorEq,ite_false,zero_add]
  ring

private theorem gaussians_sampling (S : SamplingGeometry m) (nodes : Fin n ≃ S.Node)
    (r Ds : ℝ) (main final : Fin n → ExecutableData) (layers : ℕ) :
    syntaxCount .gaussian (SamplingExecutable.build S nodes r Ds main final layers).program =
      (3+2*n+2*layers*n) + layers*(∑ i, syntaxCount .gaussian (main i).program) +
        ∑ i, syntaxCount .gaussian (final i).program := by
  change syntaxCount .gaussian (PrivateSamplingProgram.code
    (SourceExecutableTables.samplingConfig main final layers)) = _
  rw [PrivateSamplingProgram.syntaxCount_code]
  simp only [ite_true,layerInventory,SourceExecutableTables.samplingConfig,
    ← gaussianCount_eq_tapeShape,syntaxCounts]
  ring

/-- All local Gaussian instructions, including private sampling, assembly,
conditional-flow anchors, initialization and every layer's designated/residual draws. -/
def gaussianLocal (layers n ns m h : ℕ) : ℕ :=
  m+h+n+4+2*layers*n+2*(layers+1)*ns

/-- One common branching base pays local Gaussian draws and all child occurrences. -/
def fullBranching (layers n ns m h : ℕ) : ℕ :=
  max 1 (gaussianLocal layers n ns m h + (layers*n+(layers+1)*ns+m))

variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
  (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)

/-- Exact Gaussian recurrence with the four actual source child roles. -/
theorem gaussians_nonterminal (scale r σ q : ℝ) (hq : 1/2 < q) :
    syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program = gaussianLocal layers n ns m h +
    ((layers * (∑ i : Fin ns, syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w
        layers ht htq scale (S.radius r (snodes i))
        (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4)).program) +
      ∑ i : Fin ns, syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w
        layers ht htq scale (S.radius r (snodes i))
        (SourceExecutableTables.samplingFinalWidth S r) (q-1/4)).program) +
    layers * (∑ i : Fin n, syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w
      layers ht htq scale (M.radius r (nodes i))
      (RecursiveMeanPublicTable.mainWidth n r M.R Ds
        (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4)).program) +
    ∑ _i : Fin m, syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w
      layers ht htq scale (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)).program) := by
  rw [meanCore,dite_eq_right (not_le.mpr hq)]
  dsimp only [SourceMeanExecutable.build]
  rw [gaussians_sourceMean,gaussians_sampling]
  unfold gaussianLocal
  ring

/-- Gaussian-block work is bounded uniformly over all recursively generated
radii/widths and all original-gradient scales. -/
theorem gaussians_meanCore_le (scale r σ q : ℝ) :
    syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program ≤ fullBranching layers n ns m h ^ precisionRank t q := by
  let B := fullBranching layers n ns m h
  have hB : 1 ≤ B := le_max_left _ _
  suffices hall : ∀ rank : ℕ, ∀ q : ℝ, precisionRank t q = rank → ∀ r σ : ℝ,
      syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
        scale r σ q).program ≤ B ^ rank by exact hall _ q rfl r σ
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
      intro q heq r σ
      by_cases hq : q ≤ 1/2
      · rw [mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq layers scale r σ q hq]
        change 1 ≤ B^rank
        exact one_le_pow₀ hB
      · have hq' : 1/2 < q := lt_of_not_ge hq
        have hdq : precisionRank t (q-1/4)+1 ≤ rank := by
          rw [← heq]
          exact precisionRank_drop ht hq' (by linarith)
        have hdt : precisionRank t (q-t)+1 ≤ rank := by
          rw [← heq]
          exact precisionRank_drop ht hq' le_rfl
        have childQuarter (r' σ' : ℝ) : syntaxCount .gaussian
            (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              scale r' σ' (q-1/4)).program ≤ B^(rank-1) :=
          (ih _ (by omega) _ rfl r' σ').trans (pow_le_pow_right' hB (by omega))
        have childFinal (r' σ' : ℝ) : syntaxCount .gaussian
            (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              scale r' σ' (q-t)).program ≤ B^(rank-1) :=
          (ih _ (by omega) _ rfl r' σ').trans (pow_le_pow_right' hB (by omega))
        have sumQuarter (count : ℕ) (radii widths : Fin count → ℝ) :
            (∑ i, syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              scale (radii i) (widths i) (q-1/4)).program) ≤ count*B^(rank-1) := by
          calc
            _ ≤ ∑ _i : Fin count, B^(rank-1) := Finset.sum_le_sum (fun i _ => childQuarter _ _)
            _ = _ := by simp
        have sumFinal : (∑ _i : Fin m, syntaxCount .gaussian (meanCore M nodes anchors seeds S snodes
            Ds δ t w layers ht htq scale (r*M.R)
            (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)).program) ≤ m*B^(rank-1) := by
          calc
            _ ≤ ∑ _i : Fin m, B^(rank-1) := Finset.sum_le_sum (fun i _ => childFinal _ _)
            _ = _ := by simp
        rw [gaussians_nonterminal M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q hq']
        have hs := Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add (Nat.mul_le_mul_left layers (sumQuarter ns
              (fun i => S.radius r (snodes i))
              (fun _ => RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2))))
              (sumQuarter ns (fun i => S.radius r (snodes i))
                (fun _ => SourceExecutableTables.samplingFinalWidth S r)))
            (Nat.mul_le_mul_left layers (sumQuarter n
              (fun i => M.radius r (nodes i))
              (fun _ => RecursiveMeanPublicTable.mainWidth n r M.R Ds
                (SourceMeanExecutable.rowBound (m := m) r σ δ t w))))) sumFinal
        calc
          _ ≤ gaussianLocal layers n ns m h + ((layers*(ns*B^(rank-1)) + ns*B^(rank-1)) +
              layers*(n*B^(rank-1)) + m*B^(rank-1)) := Nat.add_le_add_left hs _
          _ = gaussianLocal layers n ns m h + (layers*n+(layers+1)*ns+m)*B^(rank-1) := by ring
          _ ≤ gaussianLocal layers n ns m h * B^(rank-1) +
              (layers*n+(layers+1)*ns+m)*B^(rank-1) := by
            exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by positivity : 0 < B^(rank-1))) _
          _ = (gaussianLocal layers n ns m h + (layers*n+(layers+1)*ns+m))*B^(rank-1) := by ring
          _ ≤ B*B^(rank-1) := Nat.mul_le_mul_right _ (le_max_right _ _)
          _ = B^rank := by rw [← pow_succ']; congr 1; omega

/-- Actual original-gradient calls plus Gaussian blocks, on every exact tape. -/
theorem executed_full_work_meanCore_le (scale r σ q : ℝ) (G : Point d → Point d)
    (input : Inputs d (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).size)
    (tape : Tape d (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program) :
    let counts := traceCounts (run (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program G input Env.empty tape).trace
    counts.queries + counts.gaussianBlocks ≤ 2*fullBranching layers n ns m h ^ precisionRank t q := by
  dsimp only
  rw [run_counts]
  have hbase : branching layers n ns m ≤ fullBranching layers n ns m h := by
    apply max_le (le_max_left _ _)
    exact (Nat.le_add_left _ _).trans (le_max_right _ _)
  have hq := (queries_meanCore_le M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q).trans
    (pow_le_pow_left' hbase _)
  have hg := gaussians_meanCore_le M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q
  change queryCount _ + syntaxCount .gaussian _ ≤ _
  omega

/-- The source-specialized constructor has the same every-execution complete
work cap, including both original-gradient calls and Gaussian blocks. -/
theorem executed_full_work_mean_le
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (samplingNodes : Fin ns ≃ mesh.Source m) (scale r σ q : ℝ) (G : Point d → Point d)
    (input : Inputs d (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q).size)
    (tape : Tape d (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q).program) :
    let counts := traceCounts (run (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q).program G input Env.empty tape).trace
    counts.queries + counts.gaussianBlocks ≤ 2*fullBranching layers n ns m h ^ precisionRank t q :=
  executed_full_work_meanCore_le M nodes anchors seeds (privateGeometry M mesh) samplingNodes
    Ds δ t w layers ht htq scale r σ q G input tape

end AcceleratedLogConcave.Oracle.RecursiveExecutable
