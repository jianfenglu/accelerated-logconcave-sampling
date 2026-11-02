import AcceleratedLogConcave.Root.ClockLaw
import AcceleratedLogConcave.Root.Normalization

/-! The source normalized root's fixed-inventory uniform-cell Gauss–Legendre rule.
The inventory never changes with the stopping clock, including clock zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open AcceleratedLogConcave.Numerics
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AcceleratedLogConcave.Root.ClockSchedule
abbrev Clock := ClockLaw.Clock

def sourceCells (h : ℝ) : ℕ := Nat.ceil (h ^ (-1/128 : ℝ))
def sourceOrder (K : ℕ) : ℕ := 128 * (K + 4)
lemma sourceCells_pos {h : ℝ} (hh : 0 < h) : 0 < sourceCells h :=
  Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hh _)
lemma sourceOrder_pos (K : ℕ) : 0 < sourceOrder K := by unfold sourceOrder; omega
lemma sourceOrder_eq_ceil (K : ℕ) :
    sourceOrder K = Nat.ceil (128 * ((K : ℝ) + 4)) := by
  rw [show (128 : ℝ) * ((K : ℝ) + 4) = ((128 * (K + 4) : ℕ) : ℝ) by push_cast; ring]
  exact (Nat.ceil_natCast _).symm

/-- Canonical finite enumeration of all cells and all GL nodes, fixed before clock draw. -/
def index (J m : ℕ) : Fin (J*m) ≃ Fin J × Fin m := finProdFinEquiv.symm

def unitNode (J m : ℕ) (i : Fin (J*m)) : ℝ :=
  (((index J m i).1 : ℝ) + GaussLegendre.node m (index J m i).2) / J

def nodeValue (J m : ℕ) (t : Clock) (i : Fin (J*m)) : ℝ := t * unitNode J m i

def weight (J m : ℕ) (t : Clock) (i : Fin (J*m)) : ℝ :=
  ((t : ℝ) / J) * GaussLegendre.weight m (index J m i).2

lemma unitNode_mem_Ioo (J m : ℕ) (hJ : 0 < J) (i : Fin (J*m)) :
    unitNode J m i ∈ Ioo (0 : ℝ) 1 := by
  have hj : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  rcases GaussLegendre.node_mem_Ioo m (index J m i).2 with ⟨hn0,hn1⟩
  have hc : (0 : ℝ) ≤ ((index J m i).1 : ℝ) := Nat.cast_nonneg _
  have hcJ : (((index J m i).1 : ℕ) : ℝ) + 1 ≤ J := by
    exact_mod_cast (Nat.succ_le_iff.mpr (index J m i).1.isLt)
  constructor
  · exact div_pos (by linarith) hj
  · apply (div_lt_one hj).mpr
    linarith

lemma nodeValue_mem (J m : ℕ) (hJ : 0 < J) (t : Clock) (i : Fin (J*m)) :
    nodeValue J m t i ∈ Icc (0 : ℝ) t := by
  have hu := unitNode_mem_Ioo J m hJ i
  exact ⟨mul_nonneg t.2.1 hu.1.le, mul_le_of_le_one_right t.2.1 hu.2.le⟩

/-- Actual source clock node, including its proved closed-clock membership. -/
def node (J m : ℕ) (hJ : 0 < J) (t : Clock) (i : Fin (J*m)) : Clock :=
  ⟨nodeValue J m t i, (nodeValue_mem J m hJ t i).1,
    (nodeValue_mem J m hJ t i).2.trans t.2.2⟩

lemma continuous_node (J m : ℕ) (hJ : 0 < J) (i : Fin (J*m)) :
    Continuous (fun t => node J m hJ t i) := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.mul_const _
lemma measurable_node (J m : ℕ) (hJ : 0 < J) (i : Fin (J*m)) :
    Measurable (fun t => node J m hJ t i) := (continuous_node J m hJ i).measurable
lemma measurable_weight (J m : ℕ) : Measurable (weight J m) := by
  apply Measurable.of_eval
  intro i
  unfold weight
  fun_prop

lemma weight_nonneg (J m : ℕ) (t : Clock) (i : Fin (J*m)) : 0 ≤ weight J m t i :=
  mul_nonneg (div_nonneg t.2.1 (Nat.cast_nonneg _)) (GaussLegendre.weight_pos m _).le

/-- Correct total mass rho, not 1 and not rho squared. -/
theorem sum_weight (J m : ℕ) (hJ : 0 < J) (hm : 0 < m) (t : Clock) :
    ∑ i, weight J m t i = t := by
  have he := (index J m).sum_comp (fun ij : Fin J × Fin m =>
    ((t : ℝ)/J) * GaussLegendre.weight m ij.2)
  change (∑ i, weight J m t i) = _ at he
  rw [he, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, GaussLegendre.sum_weight m hm, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma admissible (J m : ℕ) (hJ : 0 < J) (hm : 0 < m) (t : Clock) :
    AcceleratedLogConcave.Conditional.GaussianAssembly.mass (fun i => -weight J m t i) < 1 :=
  RetainedLaw.quadrature_admissible _ t (weight_nonneg J m t) (sum_weight J m hJ hm t) t.2.2

/-- The nodes really are GL nodes on uniform cells of length rho/J. -/
theorem nodeValue_eq_cellNode (J m : ℕ) (t : Clock) (i : Fin (J*m)) :
    nodeValue J m t i = GaussLegendre.cellNode m
      ((t : ℝ) * ((index J m i).1 : ℝ) / J) ((t : ℝ) / J) (index J m i).2 := by
  unfold nodeValue unitNode GaussLegendre.cellNode
  ring

theorem weight_eq_cellWeight (J m : ℕ) (t : Clock) (i : Fin (J*m)) :
    weight J m t i = GaussLegendre.cellWeight m ((t : ℝ)/J) (index J m i).2 := rfl

/-- The inventory still has J*m slots at zero clock; only the weights and nodes collapse. -/
theorem zero_node_weight (J m : ℕ) (i : Fin (J*m)) :
    nodeValue J m ⟨0, by norm_num⟩ i = 0 ∧ weight J m ⟨0, by norm_num⟩ i = 0 := by
  simp [nodeValue, weight]
end AcceleratedLogConcave.Root.ClockSchedule
