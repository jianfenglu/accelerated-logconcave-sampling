import AcceleratedLogConcave.Tensor.NetworkFamily

/-! Finite sums at one occurrence preserve route multiplicity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace AcceleratedLogConcave.Tensor.Ordered.Graph
variable {n D : ℕ} {Edge : Type*} [Fintype Edge]
variable (g : Graph n Edge) (p : Fin (n+1))

def replaceTensorAt (T : g.Tensors D) (A : Coeff (g.Slot p) D) : g.Tensors D :=
  fun v => if h : v = p then h.symm ▸ A else T v

@[simp] theorem replaceTensorAt_same (T : g.Tensors D) (A : Coeff (g.Slot p) D) :
    g.replaceTensorAt p T A p = A := by simp [replaceTensorAt]

@[simp] theorem replaceTensorAt_other (T : g.Tensors D) (A : Coeff (g.Slot p) D)
    (v : Fin (n+1)) (hv : v ≠ p) : g.replaceTensorAt p T A v = T v := by
  simp [replaceTensorAt,hv]

/-- Routes may be indexed by their list positions, so equal terms are never deduplicated. -/
theorem coordinateEval_sum_at {I : Type*} [Fintype I] (T : g.Tensors D)
    (A : I → Coeff (g.Slot p) D) (hparent : ∀ a, T p a = ∑ i, A i a) :
    g.coordinateEval D T = ∑ i, g.coordinateEval D (g.replaceTensorAt p T (A i)) := by
  unfold coordinateEval
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p), hparent, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p)]
  simp only [replaceTensorAt_same]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  rw [replaceTensorAt_other g p T (A i) v (Finset.mem_erase.mp hv).1]

end AcceleratedLogConcave.Tensor.Ordered.Graph
