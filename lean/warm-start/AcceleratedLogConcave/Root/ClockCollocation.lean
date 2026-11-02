import AcceleratedLogConcave.Numerics.AffineBounds
import AcceleratedLogConcave.Root.ClockBackwardKernel

/-! The literal outer collocation graph on the fixed clock schedule. This is
one finite affine graph; it does not assemble an outer iteration or a law. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockCollocation
open Numerics Numerics.AffineGraph
open scoped BigOperators

/-- A positive uniform partition of the unit interval. -/
def unitMesh (J : ℕ) (hJ : 0 < J) : IntervalMesh 0 1 where
  cellsPred := J-1
  point k := (k:ℝ)/J
  strictMono := by
    intro a b hab
    exact div_lt_div_of_pos_right (by exact_mod_cast hab) (Nat.cast_pos.mpr hJ)
  first := by simp
  last := by
    simp only [Fin.val_last]
    rw [Nat.sub_add_cancel (show 1 ≤ J from hJ), div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hJ))]

@[simp] theorem unitMesh_cells (J : ℕ) (hJ : 0 < J) :
    (unitMesh J hJ).cellsPred+1 = J := Nat.sub_add_cancel hJ

/-- The source schedule's enumeration, with only the actual cell-count cast. -/
def enumeration (J m : ℕ) (hJ : 0 < J) : Fin (J*m) ≃ (unitMesh J hJ).Source m :=
  (ClockSchedule.index J m).trans
    (Equiv.prodCongr (finCongr (unitMesh_cells J hJ).symm) (Equiv.refl _))

@[simp] theorem enumeration_cell (J m : ℕ) (hJ : 0 < J) (i : Fin (J*m)) :
    ((enumeration J m hJ i).1:ℕ) = ((ClockSchedule.index J m i).1:ℕ) := rfl

@[simp] theorem enumeration_node (J m : ℕ) (hJ : 0 < J) (i : Fin (J*m)) :
    (enumeration J m hJ i).2 = (ClockSchedule.index J m i).2 := rfl

theorem unitMesh_left (J : ℕ) (hJ : 0 < J) (c : (unitMesh J hJ).Cell) :
    (unitMesh J hJ).left c = (c:ℝ)/J := rfl

theorem unitMesh_length (J : ℕ) (hJ : 0 < J) (c : (unitMesh J hJ).Cell) :
    (unitMesh J hJ).length c = 1/(J:ℝ) := by
  change ((c.val+1:ℕ):ℝ)/J - (c.val:ℝ)/J = 1/(J:ℝ)
  push_cast
  ring

theorem location_enumeration (J m : ℕ) (hJ : 0 < J) (i : Fin (J*m)) :
    (unitMesh J hJ).location m (enumeration J m hJ i) = ClockSchedule.unitNode J m i := by
  rw [IntervalMesh.location, unitMesh_left, unitMesh_length]
  unfold GaussLegendre.cellNode ClockSchedule.unitNode
  simp only [enumeration_node, enumeration_cell]
  ring

abbrev count (h : ℝ) (K : ℕ) : ℕ := ClockSchedule.sourceCells h * ClockSchedule.sourceOrder K
abbrev MainIndex (h : ℝ) (K : ℕ) := Fin (count h K)

@[simp] theorem card_mainIndex (h : ℝ) (K : ℕ) : Fintype.card (MainIndex h K) = count h K :=
  Fintype.card_fin _

theorem count_pos {h : ℝ} (hh : 0 < h) (K : ℕ) : 0 < count h K :=
  Nat.mul_pos (ClockSchedule.sourceCells_pos hh) (ClockSchedule.sourceOrder_pos K)

def v (h : ℝ) (K : ℕ) (i : MainIndex h K) : ℝ :=
  ClockSchedule.unitNode (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) i
def u (h : ℝ) (K : ℕ) (clock : ClockLaw.Clock) (i : MainIndex h K) : ℝ :=
  (clock:ℝ)*v h K i
def rF (h : ℝ) : ℝ := Real.sqrt (2*h)

/-- Partial rows scaled by the stopping clock, with all fixed node labels retained. -/
def W (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock) (a : ℝ)
    (j : MainIndex h K) : ℝ :=
  (clock:ℝ)*(unitMesh (ClockSchedule.sourceCells h) (ClockSchedule.sourceCells_pos hh)).row
    (ClockSchedule.sourceOrder K) 0 a
    (enumeration _ _ (ClockSchedule.sourceCells_pos hh) j)

theorem u_eq_nodeValue (h : ℝ) (K : ℕ) (clock : ClockLaw.Clock) (i : MainIndex h K) :
    u h K clock i = ClockSchedule.nodeValue (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock i := rfl

theorem u_mem {h : ℝ} (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock) (i : MainIndex h K) :
    u h K clock i ∈ Set.Icc (0:ℝ) clock :=
  ClockSchedule.nodeValue_mem _ _ (ClockSchedule.sourceCells_pos hh) clock i

theorem W_final (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock) (j : MainIndex h K) :
    W h hh K clock 1 j = ClockSchedule.weight (ClockSchedule.sourceCells h) (ClockSchedule.sourceOrder K) clock j := by
  unfold W
  rw [IntervalMesh.row_endpoints, unitMesh_length]
  unfold GaussLegendre.cellWeight ClockSchedule.weight
  rw [enumeration_node]
  ring

theorem sum_abs_W_le (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock) (a : ℝ) :
    (∑ j, |W h hh K clock a j|) ≤ (clock:ℝ) := by
  simp only [W, abs_mul, abs_of_nonneg clock.2.1, ← Finset.mul_sum]
  rw [(enumeration _ (ClockSchedule.sourceOrder K) (ClockSchedule.sourceCells_pos hh)).sum_comp
    (fun z => |(unitMesh _ (ClockSchedule.sourceCells_pos hh)).row (ClockSchedule.sourceOrder K) 0 a z|)]
  have hr := (unitMesh _ (ClockSchedule.sourceCells_pos hh)).sum_abs_row_le
    (ClockSchedule.sourceOrder K) (ClockSchedule.sourceOrder_pos K) 0 a
  simpa using mul_le_mul_of_nonneg_left hr clock.2.1

section Graph
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Exactly the outer GL centers: no endpoint or anchor mean slots are added. -/
def graph (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock) (xF Y0 : E) :
    FiniteGraph (MainIndex h K) E where
  direct i := xF+(rF h*u h K clock i) • Y0
  matrix i j := -(rF h)^2*u h K clock i*W h hh K clock (v h K i) j
  radius i := rF h*Real.sqrt (1-(u h K clock i)^2)

theorem updateFromReplies_eq (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock)
    (xF Y0 : E) (Q : MainIndex h K → E) (i : MainIndex h K) :
    (graph h hh K clock xF Y0).updateFromReplies Q i =
      xF+(rF h*u h K clock i) • (Y0-rF h • ∑ j, W h hh K clock (v h K i) j • Q j) := by
  unfold FiniteGraph.updateFromReplies graph
  rw [smul_sub, sub_eq_add_neg, add_assoc, ← neg_smul, Finset.smul_sum, Finset.smul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem radius_eq_sourceRadius (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock)
    (xF Y0 : E) (i : MainIndex h K) :
    (graph h hh K clock xF Y0).radius i = ClockBackwardKernel.sourceRadius h hh K i clock := rfl

theorem sum_abs_matrix_le (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock)
    (xF Y0 : E) (i : MainIndex h K) :
    (∑ j, |(graph h hh K clock xF Y0).matrix i j|) ≤ (rF h)^2*(clock:ℝ)^2 := by
  have hu := u_mem hh K clock i
  simp only [graph, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (rF h)),
    abs_of_nonneg hu.1, ← Finset.mul_sum]
  calc
    _ ≤ (rF h)^2*u h K clock i*(clock:ℝ) :=
      mul_le_mul_of_nonneg_left (sum_abs_W_le h hh K clock (v h K i)) (mul_nonneg (sq_nonneg _) hu.1)
    _ ≤ (rF h)^2*(clock:ℝ)*(clock:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu.2 (sq_nonneg _)) clock.2.1
    _ = _ := by ring

theorem sum_abs_matrix_le_quarter (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock)
    (xF Y0 : E) (i : MainIndex h K) :
    (∑ j, |(graph h hh K clock xF Y0).matrix i j|) ≤ (rF h)^2/4 := by
  have hs : (clock:ℝ)^2 ≤ 1/4 := by nlinarith [clock.2.1, clock.2.2]
  exact (sum_abs_matrix_le h hh K clock xF Y0 i).trans (by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hs (sq_nonneg (rF h)))

/-- The actual request plan has every syntactic center once, even at clock zero. -/
theorem requestPlan_inventory (h : ℝ) (hh : 0 < h) (K : ℕ) (clock : ClockLaw.Clock)
    (xF Y0 : E) (old : MainIndex h K → E) :
    ((graph h hh K clock xF Y0).requestPlan old).length = count h K ∧
    (((graph h hh K clock xF Y0).requestPlan old).map Prod.fst).Nodup :=
  ⟨(FiniteGraph.requestPlan_length _ _).trans (card_mainIndex h K),
    FiniteGraph.requestPlan_labels_nodup _ _⟩

theorem clock_zero (h : ℝ) (hh : 0 < h) (K : ℕ) (xF Y0 : E)
    (Q : MainIndex h K → E) (i j : MainIndex h K) (a : ℝ) :
    u h K ⟨0,by norm_num⟩ i = 0 ∧ W h hh K ⟨0,by norm_num⟩ a j = 0 ∧
    (graph h hh K ⟨0,by norm_num⟩ xF Y0).matrix i j = 0 ∧
    (graph h hh K ⟨0,by norm_num⟩ xF Y0).radius i = rF h ∧
    (graph h hh K ⟨0,by norm_num⟩ xF Y0).updateFromReplies Q i = xF := by
  simp [u, W, graph, FiniteGraph.updateFromReplies]
end Graph
end AcceleratedLogConcave.Root.ClockCollocation
