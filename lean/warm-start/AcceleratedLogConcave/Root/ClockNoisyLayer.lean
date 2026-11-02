import AcceleratedLogConcave.Root.ClockCollocationInventory
import AcceleratedLogConcave.Oracle.NoisyLayer

/-! Literal public coefficients for one stored-center outer layer. The children
are projections of the existing mainData, not replacement programs. -/
noncomputable section
set_option autoImplicit false
namespace AcceleratedLogConcave.Root.ClockNoisyLayer
open Oracle Oracle.TapeLowering Oracle.AffineLowering Oracle.NoisyLayer
open Oracle.CovarianceSetup ClockCollocation
open scoped BigOperators MatrixOrder
variable (P : SourceSchedule)
abbrev N : ℕ := count P.delta P.K
abbrev Index := Fin (N P)

def radius (clock : ClockLaw.Clock) (i : Index P) : ℝ :=
  (graph P.delta P.delta_pos P.K clock (0:ℝ) 0).radius i
def A (clock : ClockLaw.Clock) : Mat (N P) :=
  (graph P.delta P.delta_pos P.K clock (0:ℝ) 0).matrix
def b {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) : Index P → Point d :=
  (graph P.delta P.delta_pos P.K clock xF Y0).direct
def rhoC : ℝ := rF P.delta/(4*P.Ds)
def a : ℝ := (rF P.delta)^2/4
def C (clock : ClockLaw.Clock) : Mat (N P) := residualRoot (A P clock) (rhoC P) (a P)

theorem A_literal {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) :
    A P clock = (graph P.delta P.delta_pos P.K clock xF Y0).matrix := rfl
theorem radius_literal {d : ℕ} (clock : ClockLaw.Clock) (xF Y0 : Point d) (i : Index P) :
    radius P clock i = (graph P.delta P.delta_pos P.K clock xF Y0).radius i := rfl
theorem rF_pos : 0 < rF P.delta := Real.sqrt_pos.mpr (mul_pos (by norm_num) P.delta_pos)
theorem rhoC_pos : 0 < rhoC P := div_pos (rF_pos P) (mul_pos (by norm_num) P.Ds_pos)
theorem a_pos : 0 < a P := div_pos (sq_pos_of_pos (rF_pos P)) (by norm_num)

theorem sigma_identity : sigma (N P) (rhoC P) (a P) =
    1/(2*P.Ds*Real.sqrt (N P:ℝ)*rF P.delta) := by
  have hr := ne_of_gt (rF_pos P)
  have hD := ne_of_gt P.Ds_pos
  have hn := ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (count_pos P.delta_pos P.K)))
  unfold sigma rhoC a
  field_simp

theorem sigma_width (clock : ClockLaw.Clock) (i : Index P) :
    sigma (N P) (rhoC P) (a P) = (OuterMainStability.mainState P (N P) i clock).width :=
  sigma_identity P

theorem residual_identity (clock : ClockLaw.Clock) :
    (C P clock).PosSemidef ∧ C P clock*(C P clock).transpose =
      residualCovariance (A P clock) (rhoC P) (a P) :=
  residual_root_identity (A P clock) (rhoC_pos P).le (a_pos P)
    (fun i => sum_abs_matrix_le_quarter P.delta P.delta_pos P.K clock (0:ℝ) 0 i)

theorem radius_lower (clock : ClockLaw.Clock) (i : Index P) :
    Real.sqrt 3/2*rF P.delta ≤ radius P clock i :=
  (ClockBackwardKernel.sourceRadius_mem P.delta P.delta_pos P.K i clock).1

theorem radius_ge_half (clock : ClockLaw.Clock) (i : Index P) : rF P.delta/2 ≤ radius P clock i := by
  have hs : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have hh := mul_le_mul_of_nonneg_right (show (1:ℝ)/2 ≤ Real.sqrt 3/2 by linarith) (rF_pos P).le
  exact (by nlinarith : rF P.delta/2 ≤ Real.sqrt 3/2*rF P.delta).trans (radius_lower P clock i)

theorem radius_pos (clock : ClockLaw.Clock) (i : Index P) : 0 < radius P clock i :=
  (div_pos (rF_pos P) (by norm_num : (0:ℝ) < 2)).trans_le (radius_ge_half P clock i)

theorem rhoC_le_radius (clock : ClockLaw.Clock) (i : Index P) : rhoC P ≤ radius P clock i/(2*P.Ds) := by
  have hh := div_le_div_of_nonneg_right (radius_ge_half P clock i)
    (show 0 ≤ 2*P.Ds from mul_nonneg (by norm_num) P.Ds_pos.le)
  convert hh using 1
  unfold rhoC
  ring

variable (hR : P.R ≤ 1/2) (hc : 0 < P.csch) (hsmall : P.csch < 1/160)
  (clock : ClockLaw.Clock)

/-- This is literally the already constructed standalone main-mean data. -/
abbrev child (i : Index P) : ExecutableData := OuterMainStability.mainData P hR hc hsmall (N P) i clock
abbrev c (i : Index P) : ℕ := (child P hR hc hsmall clock i).size
abbrev p (i : Index P) : Program (c P hR hc hsmall clock i) .point := (child P hR hc hsmall clock i).program
abbrev g (i : Index P) : ℕ := (tapeShape (p P hR hc hsmall clock i)).gaussianBlocks
abbrev e (i : Index P) : GaussianSlot (p P hR hc hsmall clock i) ≃ Fin (g P hR hc hsmall clock i) :=
  (child P hR hc hsmall clock i).enumeration
abbrev coeff (i : Index P) : Fin (c P hR hc hsmall clock i) → ℝ := (child P hR hc hsmall clock i).coefficient
abbrev shiftVector (i : Index P) : Fin (g P hR hc hsmall clock i) → ℝ := (child P hR hc hsmall clock i).shiftVector
def T (i : Index P) : Mat (g P hR hc hsmall clock i) :=
  childRoot (rhoC P) (radius P clock i) (shiftVector P hR hc hsmall clock i)
abbrev tableSize : ℕ := publicSize (c P hR hc hsmall clock) (p P hR hc hsmall clock)
def table : Fin (tableSize P hR hc hsmall clock) → ℝ :=
  layerTable (c P hR hc hsmall clock) (p P hR hc hsmall clock) (A P clock) (C P clock)
    (T P hR hc hsmall clock) (coeff P hR hc hsmall clock)

theorem e_literal (i : Index P) : e P hR hc hsmall clock i = gaussianSlotEquiv (p P hR hc hsmall clock i) := rfl
theorem table_a (j k : Index P) :
    table P hR hc hsmall clock (aSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) j k) = A P clock j k :=
  layerTable_a _ _ _ _ _ _ _ _
theorem table_residual (j k : Index P) :
    table P hR hc hsmall clock (residualSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) j k) = C P clock j k :=
  layerTable_residual _ _ _ _ _ _ _ _
theorem table_child (i : Index P) (k : Fin (childSize (p P hR hc hsmall clock i))) :
    table P hR hc hsmall clock (childSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) i k) =
      matrixTable (T P hR hc hsmall clock i) (coeff P hR hc hsmall clock i) k :=
  layerTable_child _ _ _ _ _ _ _ _
theorem table_matrix (i : Index P) (j k : Fin (g P hR hc hsmall clock i)) :
    table P hR hc hsmall clock (childSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) i
      (matrixIndex (c P hR hc hsmall clock i) j k)) = T P hR hc hsmall clock i j k := by
  rw [table_child]
  exact matrixTable_entry _ _ j k
theorem table_original (i : Index P) (k : Fin (c P hR hc hsmall clock i)) :
    table P hR hc hsmall clock (childSlot (c P hR hc hsmall clock) (p P hR hc hsmall clock) i
      (Fin.natAdd (g P hR hc hsmall clock i*g P hR hc hsmall clock i) k)) = coeff P hR hc hsmall clock i k :=
  layerTable_original _ _ _ _ _ _ _ _

/-- Optional numerical identity. Its paid shift bound is derived separately;
none of these schedule guards are required by the raw layer interpreter. -/
theorem child_identity (hK : 10 ≤ P.K) (hC : 8 ≤ P.Csch)
    (hy : Oracle.CubicScheduleThreshold.threshold P ≤ P.y) (i : Index P) :
    (T P hR hc hsmall clock i).PosSemidef ∧
      T P hR hc hsmall clock i*(T P hR hc hsmall clock i).transpose =
        childCovariance (rhoC P) (radius P clock i) (shiftVector P hR hc hsmall clock i) :=
  child_root_identity _ (rhoC_pos P).le (radius_pos P clock i) P.Ds_pos
    (OuterMainStability.main_queryShift_and_mass P hK hc hsmall hC hy (N P) i clock).2
    (rhoC_le_radius P clock i)

end AcceleratedLogConcave.Root.ClockNoisyLayer
