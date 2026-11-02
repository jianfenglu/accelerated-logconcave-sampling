import AcceleratedLogConcave.Root.CoolingExecutableWork
import AcceleratedLogConcave.Oracle.CubicExecutableWorkShift

/-! The fixed source schedule pays every actual lower mean call of the public
cooling constructor. The number of outer calls and local Gaussian draws remain
explicit. No accuracy, tape law, or absorbed outer cost is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal
namespace AcceleratedLogConcave.Root.CoolingSourceWork
open Oracle Numerics.AffineGraph CoolingExecutable CoolingExecutableWork
open ScalarSchedulePayment CubicScheduleThreshold ExecutableWorkCardinality

variable (Q : SourceSchedule)

/-- Concrete source data and canonical finite anchor/seed inventories. The outer
mesh is public tau=1; the inherited lower private mesh retains its own endpoint. -/
def setup (hR : Q.R ≤ 1/2) (hc : 0 < Q.csch) (hsmall : Q.csch < 1/160)
    {nc : ℕ} (mesh : IntervalMesh 0 (samplingEnd 1)) (nodes : Fin nc ≃ mesh.Source Q.m) :
    Setup Q.m (n Q hR) (CubicExecutableWorkShift.anchorCount Q hR)
      (CubicExecutableWorkShift.seedCount Q hR) (ns Q hR) nc where
  M := (CubicExecutableWorkShift.source Q hR).M
  meanNodes := (CubicExecutableWorkShift.source Q hR).nodes
  anchors := CubicExecutableWorkShift.anchors Q hR
  seeds := CubicExecutableWorkShift.seeds Q hR
  privateMesh := (CubicExecutableWorkShift.source Q hR).mesh
  privateNodes := (CubicExecutableWorkShift.source Q hR).snodes
  coolingMesh := mesh
  coolingNodes := nodes
  Ds := Q.Ds
  δ := Q.delta
  t := Q.t
  w := Q.w
  ht := Q.t_pos hc
  htq := CubicExecutableWorkShift.step_quarter Q hc hsmall
  layers := Q.NP

section Paid
variable (hK : 10 ≤ Q.K) (hc : 0 < Q.csch) (hsmall : Q.csch < 1/160)
  (hC : 8 ≤ Q.Csch) (hy : threshold Q ≤ Q.y)
local notation "hR" => CubicSchedulePayments.radius_guard Q hK hc hsmall hC hy
variable {nc d : ℕ} (mesh : IntervalMesh 0 (samplingEnd 1)) (nodes : Fin nc ≃ mesh.Source Q.m)
local notation "P" => setup Q hR hc hsmall mesh nodes

/-- The same child payment used by the mean work supplier, evaluated at the
actual public cooling child precision K. Both terminal instructions are charged. -/
theorem child_work_paid :
    ((2*workBase P ^ childRank P Q.K : ℕ) : ℝ) ≤ Real.exp (Q.y/64) := by
  have hcap := rho_add_one_le_G Q hc (by linarith : 1 ≤ Q.Csch)
  have hrank : childRank P Q.K + 1 ≤ G Q := by
    exact hcap
  have hp := absorb_leading_two (CubicExecutableWorkShift.D_ge_two Q hR)
    (CubicExecutableWorkShift.branching_le_D Q hR) hrank
  exact hp.trans (CubicSchedulePayments.actual_scalar_payments Q hK hc hsmall hC hy).2.1

/-- Query work has no local Gaussian overhead. -/
theorem executed_queries_paid (h : ℝ) (v : ℝ≥0) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v Q.K) :
    ((traceCounts (execute P h v Q.K G x ω).trace).queries : ℝ) ≤
      (occurrences P : ℝ)*Real.exp (Q.y/64) := by
  have hb : queryBase P ^ childRank P Q.K ≤ 2*workBase P ^ childRank P Q.K := by
    have hh := pow_le_pow_left' (queryBase_le_workBase P) (childRank P Q.K)
    omega
  have hq := (executed_queries_le P h v Q.K G x ω).trans
    (Nat.mul_le_mul_left (occurrences P) hb)
  have hcast : ((traceCounts (execute P h v Q.K G x ω).trace).queries : ℝ) ≤
      (occurrences P : ℝ)*((2*workBase P ^ childRank P Q.K : ℕ) : ℝ) := by
    exact_mod_cast hq
  exact hcast.trans (mul_le_mul_of_nonneg_left
    (child_work_paid Q hK hc hsmall hC hy mesh nodes) (Nat.cast_nonneg _))

/-- Original-gradient queries plus Gaussian blocks on every actual full tape.
The explicit outer multiplicity includes all fresh final children. -/
theorem executed_full_work_paid (h : ℝ) (v : ℝ≥0) (G : Point d → Point d)
    (x : Point d) (ω : FullTape P d h v Q.K) :
    (((traceCounts (execute P h v Q.K G x ω).trace).queries +
      (traceCounts (execute P h v Q.K G x ω).trace).gaussianBlocks : ℕ) : ℝ) ≤
        (localGaussians P : ℝ) + (occurrences P : ℝ)*Real.exp (Q.y/64) := by
  have hw := executed_full_work_le P h v Q.K G x ω
  have hp := child_work_paid Q hK hc hsmall hC hy mesh nodes
  have hcast : (((traceCounts (execute P h v Q.K G x ω).trace).queries +
      (traceCounts (execute P h v Q.K G x ω).trace).gaussianBlocks : ℕ) : ℝ) ≤
        (workCap P Q.K : ℝ) := by exact_mod_cast hw
  have he : (workCap P Q.K : ℝ) = (localGaussians P : ℝ) +
      (occurrences P : ℝ)*((2*workBase P ^ childRank P Q.K : ℕ) : ℝ) := by
    unfold workCap
    push_cast
    ring
  rw [he] at hcast
  exact hcast.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (occurrences P))))

/-- Finite changing-width cooling sequences, with arbitrary actual entering
states and arbitrary complete execution tapes, obey the summed source bound. -/
theorem finite_queries_paid (L : ℕ) (h : ℝ) (v : Fin L → ℝ≥0)
    (G : Point d → Point d) (x : Fin L → Point d)
    (ω : ∀ i, FullTape P d h (v i) Q.K) :
    (∑ i : Fin L, ((traceCounts (execute P h (v i) Q.K G (x i) (ω i)).trace).queries : ℝ)) ≤
      (L : ℝ)*(occurrences P : ℝ)*Real.exp (Q.y/64) := by
  calc
    _ ≤ ∑ _i : Fin L, ((occurrences P : ℝ)*Real.exp (Q.y/64)) :=
      Finset.sum_le_sum (fun i _ => executed_queries_paid Q hK hc hsmall hC hy mesh nodes h (v i) G (x i) (ω i))
    _ = _ := by simp; ring

theorem finite_full_work_paid (L : ℕ) (h : ℝ) (v : Fin L → ℝ≥0)
    (G : Point d → Point d) (x : Fin L → Point d)
    (ω : ∀ i, FullTape P d h (v i) Q.K) :
    (∑ i : Fin L, (((traceCounts (execute P h (v i) Q.K G (x i) (ω i)).trace).queries +
      (traceCounts (execute P h (v i) Q.K G (x i) (ω i)).trace).gaussianBlocks : ℕ) : ℝ)) ≤
      (L : ℝ)*((localGaussians P : ℝ)+(occurrences P : ℝ)*Real.exp (Q.y/64)) := by
  calc
    _ ≤ ∑ _i : Fin L, ((localGaussians P : ℝ)+(occurrences P : ℝ)*Real.exp (Q.y/64)) :=
      Finset.sum_le_sum (fun i _ => executed_full_work_paid Q hK hc hsmall hC hy mesh nodes h (v i) G (x i) (ω i))
    _ = _ := by simp; ring

end Paid
end AcceleratedLogConcave.Root.CoolingSourceWork
