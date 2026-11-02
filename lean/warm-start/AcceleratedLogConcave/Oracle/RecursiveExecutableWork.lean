import AcceleratedLogConcave.Oracle.RecursiveExecutable

/-! Deterministic original-gradient work of the actual well-founded source
recursion. Bounds are derived from syntax and count all private sampling,
main-layer, and active-final mean occurrences on every execution. -/
noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph TapeLowering Precision
open scoped BigOperators
variable (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
  (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
  (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
  (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4)

/-- Number of direct mean suppliers, including all suppliers in the private
finite sampler. At least one pays the terminal gradient call. -/
def branching (layers n ns m : ℕ) : ℕ := max 1 (layers*n + (layers+1)*ns + m)

theorem branching_pos : 1 ≤ branching layers n ns m := le_max_left _ _

/-- Exact recurrence of the executed nonterminal syntax, with each source
precision and physical child radius/width displayed. -/
theorem queries_nonterminal (scale r σ q : ℝ) (hq : 1/2 < q) :
    queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program =
    (layers * (∑ i : Fin ns, queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w
        layers ht htq scale (S.radius r (snodes i))
        (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4)).program) +
      ∑ i : Fin ns, queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w
        layers ht htq scale (S.radius r (snodes i))
        (SourceExecutableTables.samplingFinalWidth S r) (q-1/4)).program) +
    layers * (∑ i : Fin n, queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w
      layers ht htq scale (M.radius r (nodes i))
      (RecursiveMeanPublicTable.mainWidth n r M.R Ds
        (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4)).program) +
    ∑ _i : Fin m, queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w
      layers ht htq scale (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)).program := by
  rw [meanCore,dite_eq_right (not_le.mpr hq)]
  dsimp only [SourceMeanExecutable.build]
  rw [SourceMeanExecutable.queries_program]
  change syntaxCount .gradient (SamplingExecutable.build S snodes r Ds _ _ layers).program + _ + _ = _
  rw [SamplingExecutable.queries_build]
  rfl

/-- No work certificate is supplied: the bound follows by rank induction over
all radii and widths of the constructed recursive programs. -/
theorem queries_meanCore_le (scale r σ q : ℝ) :
    queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program ≤ branching layers n ns m ^ precisionRank t q := by
  let B := branching layers n ns m
  have hB : 1 ≤ B := branching_pos layers
  suffices hall : ∀ rank : ℕ, ∀ q : ℝ, precisionRank t q = rank → ∀ r σ : ℝ,
      queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
        scale r σ q).program ≤ B ^ rank by
    exact hall _ q rfl r σ
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
      intro q heq r σ
      by_cases hq : q ≤ 1/2
      · rw [mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq layers scale r σ q hq]
        change 1 ≤ B ^ rank
        exact one_le_pow₀ hB
      · have hq' : 1/2 < q := lt_of_not_ge hq
        have hdq : precisionRank t (q-1/4) + 1 ≤ rank := by
          rw [← heq]
          exact precisionRank_drop ht hq' (by linarith)
        have hdt : precisionRank t (q-t) + 1 ≤ rank := by
          rw [← heq]
          exact precisionRank_drop ht hq' le_rfl
        have hpos : 0 < rank := by omega
        have childQuarter (r' σ' : ℝ) :
            queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              scale r' σ' (q-1/4)).program ≤ B ^ (rank-1) := by
          exact (ih _ (by omega) _ rfl r' σ').trans (pow_le_pow_right' hB (by omega))
        have childFinal (r' σ' : ℝ) :
            queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              scale r' σ' (q-t)).program ≤ B ^ (rank-1) := by
          exact (ih _ (by omega) _ rfl r' σ').trans (pow_le_pow_right' hB (by omega))
        rw [queries_nonterminal M nodes anchors seeds S snodes Ds δ t w layers ht htq
          scale r σ q hq']
        have sumQuarter (count : ℕ) (radii widths : Fin count → ℝ) :
            (∑ i, queryCount (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              scale (radii i) (widths i) (q-1/4)).program) ≤ count * B ^ (rank-1) := by
          calc
            _ ≤ ∑ _i : Fin count, B ^ (rank-1) := Finset.sum_le_sum (fun i _ => childQuarter _ _)
            _ = _ := by simp
        have sumFinal : (∑ _i : Fin m, queryCount (meanCore M nodes anchors seeds S snodes
            Ds δ t w layers ht htq scale (r*M.R)
            (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)).program) ≤ m * B ^ (rank-1) := by
          calc
            _ ≤ ∑ _i : Fin m, B ^ (rank-1) := Finset.sum_le_sum (fun i _ => childFinal _ _)
            _ = _ := by simp
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
          _ ≤ (layers * (ns * B^(rank-1)) + ns * B^(rank-1)) +
              layers * (n * B^(rank-1)) + m * B^(rank-1) := hs
          _ = (layers*n + (layers+1)*ns + m) * B^(rank-1) := by ring
          _ ≤ B * B^(rank-1) := Nat.mul_le_mul_right _ (le_max_right _ _)
          _ = B^rank := by rw [← pow_succ']; congr 1; omega

/-- Uniform bound for the source-specialized private geometry constructed by
`mean`, still independent of the physical inputs and original-gradient scale. -/
theorem queries_mean_le (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (samplingNodes : Fin ns ≃ mesh.Source m) (scale r σ q : ℝ) :
    queryCount (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q).program ≤ branching layers n ns m ^ precisionRank t q :=
  queries_meanCore_le M nodes anchors seeds (privateGeometry M mesh) samplingNodes
    Ds δ t w layers ht htq scale r σ q

/-- Every supplied tape and original-gradient oracle has this deterministic cap. -/
theorem executed_queries_meanCore_le (scale r σ q : ℝ) (G : Point d → Point d)
    (input : Inputs d (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).size)
    (tape : Tape d (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program) :
    (traceCounts (run (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q).program G input Env.empty tape).trace).queries ≤
        branching layers n ns m ^ precisionRank t q := by
  rw [run_counts]
  exact queries_meanCore_le M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q

/-- The source-specialized constructor has the same cap on every execution. -/
theorem executed_queries_mean_le
    (mesh : IntervalMesh 0 (samplingEnd (M.R/backwardEnd M.R)))
    (samplingNodes : Fin ns ≃ mesh.Source m) (scale r σ q : ℝ) (G : Point d → Point d)
    (input : Inputs d (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q).size)
    (tape : Tape d (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q).program) :
    (traceCounts (run (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q).program G input Env.empty tape).trace).queries ≤
        branching layers n ns m ^ precisionRank t q := by
  rw [run_counts]
  exact queries_mean_le M nodes anchors seeds Ds δ t w layers ht htq mesh samplingNodes scale r σ q

end AcceleratedLogConcave.Oracle.RecursiveExecutable
