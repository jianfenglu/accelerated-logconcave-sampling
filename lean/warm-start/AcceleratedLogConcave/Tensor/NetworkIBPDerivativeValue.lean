import AcceleratedLogConcave.Tensor.NetworkIBPPorts

noncomputable section
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
open AdjointReduction ReductionRecords

theorem partialAlong_map_directions {V L M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : M → V) (f : L → M) (J : List L) (F : V → ℝ) :
    partialAlong d (J.map f) F = partialAlong (fun u => d (f u)) J F := by
  induction J with
  | nil => rfl
  | cons u J ih => simp only [List.map_cons, partialAlong, ih]

theorem partialAlong_finRange_head {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : ℕ) (d : Fin (a+1) → V) (F : V → ℝ) :
    partialAlong d (List.finRange (a+1)) F =
      dir (d 0) (partialAlong (fun u : Fin a => d u.succ) (List.finRange a) F) := by
  rw [List.finRange_succ]
  simp only [partialAlong, partialAlong_map_directions]

end AcceleratedLogConcave.Tensor.Ordered.Graph
