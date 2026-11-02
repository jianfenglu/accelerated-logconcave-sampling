import AcceleratedLogConcave.Oracle.RecursiveExecutable

/-! Induction over the actual precision-indexed executable. Its four induction
hypotheses concern exactly the main mean calls, active-final mean calls, private
sampling main mean calls, and private sampling final mean calls constructed by
`meanCore`. The predicate can inspect the full actual executable data. This is
an induction principle, not an accuracy, coupling, or law certificate. -/

noncomputable section
namespace AcceleratedLogConcave.Oracle.RecursiveExecutable
open Numerics.AffineGraph TapeLowering Precision

variable {m n a h ms ns : ℕ}
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1/4) (scale : ℝ)
    (P : ℝ → ℝ → ℝ → ExecutableData → Prop)

variable
    (hterminal : ∀ r σ q, q ≤ 1/2 → P r σ q (terminal scale r σ))
    (hstep : ∀ r σ q, (1/2 : ℝ) < q →
      (∀ i : Fin n,
        P (M.radius r (nodes i))
          (RecursiveMeanPublicTable.mainWidth n r M.R Ds
            (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4)
          (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale (M.radius r (nodes i))
            (RecursiveMeanPublicTable.mainWidth n r M.R Ds
              (SourceMeanExecutable.rowBound (m := m) r σ δ t w)) (q-1/4))) →
      (∀ _i : Fin m,
        P (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t)
          (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale (r*M.R) (RecursiveMeanPublicTable.finalWidth M.R σ) (q-t))) →
      (∀ i : Fin ns,
        P (S.radius r (snodes i))
          (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4)
          (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale (S.radius r (snodes i))
            (RecursiveMeanPublicTable.mainWidth ns r S.R Ds (r^2)) (q-1/4))) →
      (∀ i : Fin ns,
        P (S.radius r (snodes i)) (SourceExecutableTables.samplingFinalWidth S r) (q-1/4)
          (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale (S.radius r (snodes i)) (SourceExecutableTables.samplingFinalWidth S r) (q-1/4))) →
      P r σ q (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q))

include hterminal hstep

/-- Exact four-child well-founded induction for the constructed executable.
No admissibility, stability, accuracy or law is supplied. -/
theorem meanCore_induction (r σ q : ℝ) : P r σ q (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q) := by
  apply meanCore.induct M nodes anchors seeds S snodes Ds δ t w layers ht htq scale
    (fun r σ q => P r σ q (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q))
  · intro r σ q hq
    rw [mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq layers scale r σ q hq]
    exact hterminal r σ q hq
  · intro r σ q hq hm hf hsm hsf
    exact hstep r σ q (lt_of_not_ge hq) hm (fun _ => hf) hsm hsf

/-- Fuel-indexed interface to the same well-founded induction. The actual
construction terminates independently of an external choice of fuel. -/
theorem meanCore_induction_fuel (fuel : ℕ) (r σ q : ℝ)
    (_hRank : precisionRank t q ≤ fuel) : P r σ q (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq scale r σ q) :=
  meanCore_induction M nodes anchors seeds S snodes Ds δ t w layers ht htq scale
    P hterminal hstep r σ q

end AcceleratedLogConcave.Oracle.RecursiveExecutable
