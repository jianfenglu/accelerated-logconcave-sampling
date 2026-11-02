import AcceleratedLogConcave.Oracle.RecursiveExecutable

/-! Structural parameter independence for the actual source recursion. The
syntax carrier is the dependent pair of register count and literal program;
coefficient and shift data remain separate parameter-dependent fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace AcceleratedLogConcave.Oracle.RecursiveExecutableParameterShape
open RecursiveExecutable TapeLowering Numerics.AffineGraph Precision

def shape (E : ExecutableData) : Σ c : ℕ, Program c .point :=
  ⟨E.size, E.program⟩

def canonicalData (s : Σ c : ℕ, Program c .point) : ExecutableData where
  size := s.1
  program := s.2
  coefficient := fun _ => 0
  shift := fun _ => 0

@[simp] theorem shape_canonicalData (s : Σ c : ℕ, Program c .point) :
    shape (canonicalData s) = s := by
  cases s
  rfl

theorem sampling_build_shape {ms ns : ℕ}
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (r Ds r' Ds' : ℝ) (layers : ℕ)
    (main main' final final' : Fin ns → ExecutableData)
    (hm : ∀ i, shape (main i) = shape (main' i))
    (hf : ∀ i, shape (final i) = shape (final' i)) :
    shape (SamplingExecutable.build S snodes r Ds main final layers) =
      shape (SamplingExecutable.build S snodes r' Ds' main' final' layers) := by
  have hmn : (fun i => canonicalData (shape (main i))) =
      (fun i => canonicalData (shape (main' i))) := by
    funext i
    exact congrArg canonicalData (hm i)
  have hfn : (fun i => canonicalData (shape (final i))) =
      (fun i => canonicalData (shape (final' i))) := by
    funext i
    exact congrArg canonicalData (hf i)
  calc
    shape (SamplingExecutable.build S snodes r Ds main final layers) =
      shape (SamplingExecutable.build S snodes r Ds
        (fun i => canonicalData (shape (main i)))
        (fun i => canonicalData (shape (final i))) layers) := rfl
    _ = shape (SamplingExecutable.build S snodes r' Ds'
        (fun i => canonicalData (shape (main' i)))
        (fun i => canonicalData (shape (final' i))) layers) := by
          rw [hmn, hfn]
          rfl
    _ = shape (SamplingExecutable.build S snodes r' Ds' main' final' layers) := rfl

theorem source_build_shape {m n a h : ℕ}
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (r σ Ds δ t w r' σ' Ds' δ' t' w' : ℝ) (layers : ℕ)
    (main main' : Fin n → ExecutableData)
    (final final' : Fin m → ExecutableData)
    (sampling sampling' : ExecutableData)
    (shift : GaussianSlot sampling.program → ℝ)
    (shift' : GaussianSlot sampling'.program → ℝ)
    (hm : ∀ i, shape (main i) = shape (main' i))
    (hf : ∀ i, shape (final i) = shape (final' i))
    (hs : shape sampling = shape sampling') :
    shape (SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w
      main final sampling layers shift) =
    shape (SourceMeanExecutable.build M nodes anchors seeds r' σ' Ds' δ' t' w'
      main' final' sampling' layers shift') := by
  have hmn : (fun i => canonicalData (shape (main i))) =
      (fun i => canonicalData (shape (main' i))) := by
    funext i
    exact congrArg canonicalData (hm i)
  have hfn : (fun i => canonicalData (shape (final i))) =
      (fun i => canonicalData (shape (final' i))) := by
    funext i
    exact congrArg canonicalData (hf i)
  have hsn : canonicalData (shape sampling) = canonicalData (shape sampling') :=
    congrArg canonicalData hs
  calc
    shape (SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w
      main final sampling layers shift) =
      shape (SourceMeanExecutable.build M nodes anchors seeds r σ Ds δ t w
        (fun i => canonicalData (shape (main i)))
        (fun i => canonicalData (shape (final i)))
        (canonicalData (shape sampling)) layers (fun _ => 0)) := rfl
    _ = shape (SourceMeanExecutable.build M nodes anchors seeds r' σ' Ds' δ' t' w'
        (fun i => canonicalData (shape (main' i)))
        (fun i => canonicalData (shape (final' i)))
        (canonicalData (shape sampling')) layers (fun _ => 0)) := by
          rw [hmn, hfn, hsn]
          rfl
    _ = shape (SourceMeanExecutable.build M nodes anchors seeds r' σ' Ds' δ' t' w'
        main' final' sampling' layers shift') := rfl

theorem terminal_shape (scale r σ scale' r' σ' : ℝ) :
    shape (RecursiveExecutable.terminal scale r σ) =
      shape (RecursiveExecutable.terminal scale' r' σ') := rfl

variable {m n a h ms ns : ℕ}
    (M : MeanGeometry m) (nodes : Fin n ≃ M.MeanNode)
    (anchors : Fin a ≃ M.Anchor) (seeds : Fin h ≃ Fin m × M.Kernel)
    (S : SamplingGeometry ms) (snodes : Fin ns ≃ S.Node)
    (Ds δ t w : ℝ) (layers : ℕ) (ht : 0 < t) (htq : t ≤ 1 / 4)

/-- The actual recursive program's register count and syntax are independent
of all physical scale, radius and width parameters at fixed precision. -/
theorem meanCore_shape (q scale r σ scale' r' σ' : ℝ) :
    shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale r σ q) =
    shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
      scale' r' σ' q) := by
  suffices hall : ∀ rank : ℕ, ∀ q : ℝ, precisionRank t q = rank →
      ∀ scale r σ scale' r' σ' : ℝ,
      shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
        scale r σ q) =
      shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
        scale' r' σ' q) by
    exact hall _ q rfl scale r σ scale' r' σ'
  intro rank
  induction rank using Nat.strong_induction_on with
  | h rank ih =>
      intro q heq scale r σ scale' r' σ'
      by_cases hq : q ≤ 1 / 2
      · rw [mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq
          layers scale r σ q hq,
          mean_terminal M nodes anchors seeds S snodes Ds δ t w ht htq
          layers scale' r' σ' q hq]
        exact terminal_shape scale r σ scale' r' σ'
      · have hq' : 1 / 2 < q := lt_of_not_ge hq
        have hquarter : precisionRank t (q - 1 / 4) < rank := by
          have hd := precisionRank_drop ht hq' (show q - 1 / 4 ≤ q - t by linarith)
          omega
        have hfinal : precisionRank t (q - t) < rank := by
          have hd := precisionRank_drop ht hq' (show q - t ≤ q - t from le_rfl)
          omega
        have iq (s u v s' u' v' : ℝ) :
            shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              s u v (q - 1 / 4)) =
            shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              s' u' v' (q - 1 / 4)) := ih _ hquarter _ rfl s u v s' u' v'
        have it (s u v s' u' v' : ℝ) :
            shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              s u v (q - t)) =
            shape (meanCore M nodes anchors seeds S snodes Ds δ t w layers ht htq
              s' u' v' (q - t)) := ih _ hfinal _ rfl s u v s' u' v'
        conv_lhs => rw [meanCore, dite_eq_right hq]
        conv_rhs => rw [meanCore, dite_eq_right hq]
        apply source_build_shape M nodes anchors seeds
        · intro i
          exact iq _ _ _ _ _ _
        · intro i
          exact it _ _ _ _ _ _
        · apply sampling_build_shape S snodes
          · intro i
            exact iq _ _ _ _ _ _
          · intro i
            exact iq _ _ _ _ _ _

/-- The source-specialized public constructor inherits parameter-independent
register count and literal syntax at fixed precision. -/
theorem mean_shape
    (mesh : IntervalMesh 0 (samplingEnd (M.R / backwardEnd M.R)))
    (samplingNodes : Fin ns ≃ mesh.Source m)
    (q scale r σ scale' r' σ' : ℝ) :
    shape (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale r σ q) =
    shape (mean M nodes anchors seeds Ds δ t w ht htq layers mesh samplingNodes
      scale' r' σ' q) :=
  meanCore_shape M nodes anchors seeds (privateGeometry M mesh) samplingNodes
    Ds δ t w layers ht htq q scale r σ scale' r' σ'

end AcceleratedLogConcave.Oracle.RecursiveExecutableParameterShape
