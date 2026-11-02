import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Finite synchronous collocation and maximum-of-node-L2 error bounds

The scalar recurrence and prescribed finite update count follow
`sources/warm-start.tex:2463–2465, 2518–2522, 2659–2660, 2876–2900, 3202`.
`layerCount_ge_strong` separately pays the stronger count at source3233.

The generic map lemmas retain explicit rowwise Lipschitz, reference residual,
and update perturbation hypotheses. They do not establish those hypotheses for
the actual affine graph. The noisy source compiler additionally needs its joint
coupling and cancellation identity; neither Gaussian marginals nor independence
are manufactured by this module. The L2 norm is taken before the finite-node
maximum, with an explicit `MemLp` witness for raw error fields.

All iterates are finite. `layer_node_slots_card` counts a finite index set;
connecting it to actual stored-reply evaluations and recursive gradient work is
a separate adapter obligation. No graph, mesh, RMS quadrature, root-import, or
source-schedule integration is asserted here.
-/

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators NNReal
noncomputable section
namespace AcceleratedLogConcave.Numerics.Collocation


def iteratePhi {S : Type*} (Phi : S → S) (initial : S) (N : ℕ) : S :=
  (Phi^[N]) initial

def forcingSum (q : ℝ) (eta : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, q ^ (N - 1 - k) * eta k

def nodeError {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    (x y : ι → V) : ℝ := ‖x - y‖

def nodeL2Norm {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (d : ι → Lp E 2 μ) : ℝ := ‖d‖

def rawNodeErrorNorm {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (err : ι → Ω → E)
    (herr : ∀ i, MemLp (err i) 2 μ) : ℝ :=
  nodeL2Norm μ (fun i => (herr i).toLp (err i))

def layerCount (C K : ℝ) : ℕ := ⌈C * (K + 2)⌉₊



theorem iteratePhi_zero {S : Type*} (Phi : S → S) (initial : S) :
  iteratePhi Phi initial 0 = initial := by
  rfl

theorem iteratePhi_succ {S : Type*} (Phi : S → S)
    (initial : S) (N : ℕ) :
  iteratePhi Phi initial (N + 1) = Phi (iteratePhi Phi initial N) := by
  exact Function.iterate_succ_apply' Phi N initial

theorem layer_node_slots_card (ι : Type*) [Fintype ι] (N : ℕ) :
  Fintype.card (Fin N × ι) = N * Fintype.card ι := by
  simp

theorem forcingSum_zero (q : ℝ) (eta : ℕ → ℝ) :
  forcingSum q eta 0 = 0 := by
  simp [forcingSum]

theorem forcingSum_succ (q : ℝ) (eta : ℕ → ℝ) (N : ℕ) :
  forcingSum q eta (N + 1) = q * forcingSum q eta N + eta N := by
  unfold forcingSum
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hexp : N - k = (N - 1 - k) + 1 := by
    have hlt := Finset.mem_range.mp hk
    omega
  rw [hexp, pow_succ', mul_assoc]

theorem forcingSum_const (q eta : ℝ) (N : ℕ) :
  forcingSum q (fun _ => eta) N = eta * ∑ j ∈ Finset.range N, q ^ j := by
  induction N with
  | zero => simp [forcingSum_zero]
  | succ N ih =>
      rw [forcingSum_succ, ih, geom_sum_succ]
      ring

theorem error_le_finite_sum (e eta : ℕ → ℝ) (q : ℝ) (N : ℕ)
    (hq : 0 ≤ q)
    (recurrence : ∀ k < N, e (k + 1) ≤ q * e k + eta k) :
  e N ≤ q ^ N * e 0 + forcingSum q eta N := by
  revert recurrence
  induction N with
  | zero =>
      intro _
      simp [forcingSum_zero]
  | succ N ih =>
      intro recurrence
      have hprev := ih (fun k hk => recurrence k (Nat.lt_succ_of_lt hk))
      calc
        e (N + 1) ≤ q * e N + eta N := recurrence N (Nat.lt_succ_self N)
        _ ≤ q * (q ^ N * e 0 + forcingSum q eta N) + eta N :=
          add_le_add (mul_le_mul_of_nonneg_left hprev hq) le_rfl
        _ = q ^ (N + 1) * e 0 + forcingSum q eta (N + 1) := by
          rw [forcingSum_succ, pow_succ']
          ring

theorem error_le_uniform_finite_sum (e : ℕ → ℝ) (q eta : ℝ) (N : ℕ)
    (hq : 0 ≤ q)
    (recurrence : ∀ k < N, e (k + 1) ≤ q * e k + eta) :
  e N ≤ q ^ N * e 0 + eta * ∑ j ∈ Finset.range N, q ^ j := by
  simpa only [forcingSum_const] using
    error_le_finite_sum e (fun _ => eta) q N hq recurrence

theorem error_le_uniform_geometric (e : ℕ → ℝ) (q eta : ℝ) (N : ℕ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (heta : 0 ≤ eta)
    (recurrence : ∀ k < N, e (k + 1) ≤ q * e k + eta) :
  e N ≤ q ^ N * e 0 + eta / (1 - q) := by
  have hsum : (∑ j ∈ Finset.range N, q ^ j) ≤ 1 / (1 - q) := by
    simpa using (geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hq0 hq1)
  calc
    e N ≤ q ^ N * e 0 + eta * ∑ j ∈ Finset.range N, q ^ j :=
      error_le_uniform_finite_sum e q eta N hq0 recurrence
    _ ≤ q ^ N * e 0 + eta * (1 / (1 - q)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum heta)
    _ = q ^ N * e 0 + eta / (1 - q) := by simp [div_eq_mul_inv]

theorem error_zero_contraction (e eta : ℕ → ℝ) (N : ℕ)
    (recurrence : ∀ k < N + 1, e (k + 1) ≤ (0 : ℝ) * e k + eta k) :
  e (N + 1) ≤ eta N := by
  simpa using recurrence N (Nat.lt_succ_self N)



theorem nodeError_eq_sup {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] (x y : ι → V) :
  nodeError x y = ((Finset.univ.sup (fun i => ‖x i - y i‖₊) : ℝ≥0) : ℝ) := by
  rfl

theorem nodeError_empty {ι V : Type*} [Fintype ι] [IsEmpty ι]
    [NormedAddCommGroup V] (x y : ι → V) :
 nodeError x y = 0 := by
  rw [nodeError_eq_sup]
  simp

theorem nodeError_step {ι V : Type*} [Fintype ι] [NormedAddCommGroup V]
    (Phi : ℕ → (ι → V) → (ι → V)) (x reference : ℕ → ι → V)
    (q : ℝ) (residual perturbation : ℕ → ℝ) (N : ℕ)
    (hq : 0 ≤ q)
    (hresidual : ∀ k < N, 0 ≤ residual k)
    (hperturbation : ∀ k < N, 0 ≤ perturbation k)
    (rowwiseLipschitz : ∀ k < N, ∀ u v : ι → V, ∀ i,
      ‖Phi k u i - Phi k v i‖ ≤ q * nodeError u v)
    (referenceResidual : ∀ k < N, ∀ i,
      ‖Phi k (reference k) i - reference (k + 1) i‖ ≤ residual k)
    (updatePerturbation : ∀ k < N, ∀ i,
      ‖x (k + 1) i - Phi k (x k) i‖ ≤ perturbation k) :
  ∀ k < N, nodeError (x (k + 1)) (reference (k + 1)) ≤
    q * nodeError (x k) (reference k) + (residual k + perturbation k) := by
  intro k hk
  have hbudget : 0 ≤ q * nodeError (x k) (reference k) +
      (residual k + perturbation k) :=
    add_nonneg (mul_nonneg hq (norm_nonneg _))
      (add_nonneg (hresidual k hk) (hperturbation k hk))
  apply (pi_norm_le_iff_of_nonneg hbudget).2
  intro i
  change ‖x (k + 1) i - reference (k + 1) i‖ ≤ _
  have htri₁ := dist_triangle (x (k + 1) i) (Phi k (x k) i) (reference (k + 1) i)
  have htri₂ := dist_triangle (Phi k (x k) i) (Phi k (reference k) i)
    (reference (k + 1) i)
  simp only [dist_eq_norm] at htri₁ htri₂
  have hrow := rowwiseLipschitz k hk (x k) (reference k) i
  have hres := referenceResidual k hk i
  have hpert := updatePerturbation k hk i
  linarith

theorem iteratePhi_error_le {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] (Phi : (ι → V) → (ι → V))
    (initial reference : ι → V) (q residual : ℝ) (N : ℕ)
    (hq : 0 ≤ q) (hresidual : 0 ≤ residual)
    (rowwiseLipschitz : ∀ u v : ι → V, ∀ i,
      ‖Phi u i - Phi v i‖ ≤ q * nodeError u v)
    (referenceResidual : ∀ i, ‖Phi reference i - reference i‖ ≤ residual) :
  nodeError (iteratePhi Phi initial N) reference ≤
    q ^ N * nodeError initial reference +
      residual * ∑ j ∈ Finset.range N, q ^ j := by
  have hstep := nodeError_step (fun _ => Phi)
    (fun k => iteratePhi Phi initial k) (fun _ => reference)
    q (fun _ => residual) (fun _ => 0) N hq
    (fun _ _ => hresidual) (fun _ _ => le_rfl)
    (fun _ _ => rowwiseLipschitz) (fun _ _ => referenceResidual)
    (by
      intro k _ i
      rw [iteratePhi_succ]
      simp)
  have hbound := error_le_uniform_finite_sum
    (fun k => nodeError (iteratePhi Phi initial k) reference) q residual N hq
    (fun k hk => by simpa using hstep k hk)
  simpa only [iteratePhi_zero] using hbound

theorem nodeL2Norm_eq_sup {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (d : ι → Lp E 2 μ) :
  nodeL2Norm μ d = ((Finset.univ.sup (fun i => ‖d i‖₊) : ℝ≥0) : ℝ) := by
  rfl

theorem rawNodeErrorNorm_eq_sup {ι Ω E : Type*}
    [Fintype ι] [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (err : ι → Ω → E) (herr : ∀ i, MemLp (err i) 2 μ) :
  rawNodeErrorNorm μ err herr =
    ((Finset.univ.sup (fun i => (eLpNorm (err i) 2 μ).toNNReal) : ℝ≥0) : ℝ) := by
  simp only [rawNodeErrorNorm, nodeL2Norm_eq_sup, Lp.nnnorm_toLp]

theorem nodeL2Norm_error_le {ι Ω E : Type*} [Fintype ι] [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) (d : ℕ → ι → Lp E 2 μ)
    (q : ℝ) (eta : ℕ → ℝ) (N : ℕ) (hq : 0 ≤ q)
    (heta : ∀ k < N, 0 ≤ eta k)
    (rowwiseRecurrence : ∀ k < N, ∀ i,
      ‖d (k + 1) i‖ ≤ q * nodeL2Norm μ (d k) + eta k) :
  nodeL2Norm μ (d N) ≤
    q ^ N * nodeL2Norm μ (d 0) + forcingSum q eta N := by
  apply error_le_finite_sum (fun k => nodeL2Norm μ (d k)) eta q N hq
  intro k hk
  have hbudget : 0 ≤ q * nodeL2Norm μ (d k) + eta k :=
    add_nonneg (mul_nonneg hq (norm_nonneg _)) (heta k hk)
  exact (pi_norm_le_iff_of_nonneg hbudget).2 (rowwiseRecurrence k hk)



theorem layerCount_lower (C K : ℝ) :
  C * (K + 2) ≤ (layerCount C K : ℝ) :=
  Nat.le_ceil _

theorem layerCount_upper (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K) :
  (layerCount C K : ℝ) < C * (K + 2) + 1 := by
  exact Nat.ceil_lt_add_one (mul_nonneg hC (by linarith))

theorem layerCount_ge_three (C K : ℝ) (hC : 3 ≤ C) (hK : 0 ≤ K) :
  3 * (K + 2) ≤ (layerCount C K : ℝ) := by
  exact (mul_le_mul_of_nonneg_right hC (by linarith)).trans (layerCount_lower C K)

theorem contraction_pow_le_source (q delta K : ℝ) (N : ℕ)
    (hq : 0 ≤ q) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hcontraction : q ≤ delta ^ (1 / 3 : ℝ))
    (hcount : 3 * (K + 2) ≤ (N : ℝ)) :
    q ^ N ≤ delta ^ (K + 2) := by
  calc
    q ^ N ≤ (delta ^ (1 / 3 : ℝ)) ^ N := pow_le_pow_left₀ hq hcontraction N
    _ = delta ^ ((1 / 3 : ℝ) * (N : ℝ)) :=
      (Real.rpow_mul_natCast hdelta0.le (1 / 3 : ℝ) N).symm
    _ ≤ delta ^ (K + 2) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta0 hdelta1 (by linarith)

theorem error_le_at_layerCount (e : ℕ → ℝ) (q delta C K E0 eta : ℝ)
    (hq : 0 ≤ q) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hcontraction : q ≤ delta ^ (1 / 3 : ℝ))
    (hC : 3 ≤ C) (hK : 0 ≤ K) (hE0 : 0 ≤ E0) (heta : 0 ≤ eta)
    (initialError : e 0 ≤ E0)
    (recurrence : ∀ k < layerCount C K, e (k + 1) ≤ q * e k + eta) :
  e (layerCount C K) ≤ delta ^ (K + 2) * E0 + eta / (1 - q) := by
  have hq1 : q < 1 := hcontraction.trans_lt
    (Real.rpow_lt_one hdelta0.le hdelta1 (by norm_num))
  have hpower : q ^ layerCount C K ≤ delta ^ (K + 2) :=
    contraction_pow_le_source q delta K (layerCount C K) hq hdelta0 hdelta1.le
      hcontraction (layerCount_ge_three C K hC hK)
  calc
    e (layerCount C K) ≤ q ^ layerCount C K * e 0 + eta / (1 - q) :=
      error_le_uniform_geometric e q eta (layerCount C K) hq hq1 heta recurrence
    _ ≤ q ^ layerCount C K * E0 + eta / (1 - q) :=
      add_le_add (mul_le_mul_of_nonneg_left initialError
        (pow_nonneg hq _)) le_rfl
    _ ≤ delta ^ (K + 2) * E0 + eta / (1 - q) :=
      add_le_add (mul_le_mul_of_nonneg_right hpower hE0) le_rfl

-- Separate source3233 numerical-certificate obligation; not the compiler count.
theorem layerCount_ge_strong (C K : ℝ) (hC : 10 ≤ C) (hK : 10 ≤ K) :
  2 * K + 20 ≤ (layerCount C K : ℝ) / 3 := by
  have hscale : 10 * (K + 2) ≤ (layerCount C K : ℝ) :=
    (mul_le_mul_of_nonneg_right hC (by linarith)).trans (layerCount_lower C K)
  linarith




end AcceleratedLogConcave.Numerics.Collocation
