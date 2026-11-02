import AcceleratedLogConcave.Numerics.AffineBounds
import AcceleratedLogConcave.Numerics.Collocation
import AcceleratedLogConcave.Numerics.RmsQuadrature
import AcceleratedLogConcave.Numerics.SingularKernelQuadrature

/-!
# AffineQuadrature

Actual signed mesh, endpoint derivative, and singular Option-origin quadrature.
The analytic inputs are genuine derivative regularity and endpoint identities.
-/

noncomputable section AffineQuadratureQuadratureDefs
open MeasureTheory Set
open scoped BigOperators ContDiff
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def cellBudget {lo hi : ℝ} (M : IntervalMesh lo hi) (m : ℕ)
    (D : M.Cell → ℝ) : ℝ :=
  ∑ c, 2 * (M.length c) ^ (m+1) * D c / (m.factorial : ℝ)

def CellRegularity {lo hi : ℝ} (M : IntervalMesh lo hi) (m : ℕ)
    (f : ℝ → E) (D : M.Cell → ℝ) : Prop :=
  (∀ c, 0 ≤ D c) ∧
  (∀ c, ∀ t ∈ Icc (M.left c) (M.right c), ContDiffAt ℝ m f t) ∧
  (∀ c, ∀ t ∈ Icc (M.left c) (M.right c), ‖iteratedDeriv m f t‖ ≤ D c)

def IntervalRowDefectStatement : Prop :=
  ∀ {lo hi : ℝ} (M : IntervalMesh lo hi) (m : ℕ), 1 ≤ m →
  ∀ (u v : ℝ), u ∈ Icc lo hi → v ∈ Icc lo hi →
  ∀ (f : ℝ → E) (D : M.Cell → ℝ), CellRegularity M m f D →
    ‖(∫ t in u..v, f t) - ∑ j, M.row m u v j • f (M.location m j)‖ ≤
      cellBudget M m D

def AngleDerivativeDefectStatement : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (ψ D : ℝ), 0 < ψ → 0 ≤ D →
  ∀ (f : ℝ → E),
    (∀ t ∈ Icc (0:ℝ) ψ, ContDiffAt ℝ m f t) →
    (∀ t ∈ Icc (0:ℝ) ψ, ‖iteratedDeriv m f t‖ ≤ D) →
    ‖deriv f 0 - ∑ j : Fin m, GaussLegendre.derivativeRow m 0 ψ 0 j •
      f (GaussLegendre.cellNode m 0 ψ j)‖ ≤
      (m:ℝ)^3 * ψ^(m-1) * D / (m.factorial:ℝ)

def KernelDefectStatement : Prop :=
  ∀ (m : ℕ) (G : MeanGeometry m), 1 ≤ m →
  ∀ (l u A h₀ : ℝ), l < 0 → backwardEnd G.R < u → 0 ≤ A → 0 ≤ h₀ →
  (∀ c, G.backward.length c ≤ 2*h₀*(1-(G.backward.right c)^2)) →
  ∀ (f : ℝ → E), ContDiffOn ℝ (m+2) f (Ioo l u) →
    deriv f 0 = 0 → f (backwardEnd G.R) = 0 →
    (∀ t ∈ Icc (0:ℝ) (backwardEnd G.R),
      ‖iteratedDeriv (m+2) f t‖ ≤ A/(1-t^2)^(m+2)) →
    ‖(∫ t in 0..backwardEnd G.R, t⁻¹ • deriv f t) -
      ∑ ρ : G.Kernel, G.kernelCoeff ρ • f (G.rho ρ)‖ ≤
      (16:ℝ)^m*A*h₀^m/(m.factorial:ℝ)

end AcceleratedLogConcave.Numerics.AffineResidual
end AffineQuadratureQuadratureDefs

noncomputable section AffineQuadratureRows
/-!

-/

open MeasureTheory Polynomial Set
open scoped BigOperators
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def gaussValueRow (n : ℕ) (a h u v : ℝ) (κ : ℝ → ℝ) : ValueRow (Fin n) where
  node := GaussLegendre.cellNode n a h
  weight := GaussLegendre.partialRow n a h u v κ
  start := a+h*u
  finish := a+h*v

theorem partialRow_monomial_exactness (n : ℕ) (a h u v : ℝ) (hh : 0 < h)
    (κ : ℝ → ℝ) (hi : IntervalIntegrable κ volume (a+h*u) (a+h*v)) :
    (gaussValueRow n a h u v κ).Exact κ a n := by
  intro j hj
  have hp : (((X-C a)^j : ℝ[X])).degree < n := by
    rw [degree_pow, degree_X_sub_C]
    simpa using hj
  simpa [gaussValueRow] using GaussLegendre.partialRow_reproduces n a h u v hh κ hi
    ((X-C a)^j) hp

/-- Concrete Gauss–Legendre nodes and actual signed partial integration weights
supply every scalar premise of the sharp Banach/RMS defect theorem. -/
theorem norm_partialRow_defect_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) (hn : 1 ≤ n) (a h u v : ℝ) (hh : 0 < h)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1)
    (κ : ℝ → ℝ) (hi : IntervalIntegrable κ volume (a+h*u) (a+h*v))
    (hk : ∀ y ∈ uIcc (a+h*u) (a+h*v), |κ y| ≤ 1)
    (f : ℝ → E) (D : ℝ) (hD0 : 0 ≤ D)
    (hf : ∀ y ∈ Icc a (a+h), ContDiffAt ℝ n f y)
    (hD : ∀ y ∈ Icc a (a+h), ‖iteratedDeriv n f y‖ ≤ D) :
    ‖(∫ y in (a+h*u)..(a+h*v), κ y • f y) -
      ∑ i : Fin n, GaussLegendre.partialRow n a h u v κ i •
        f (GaussLegendre.cellNode n a h i)‖ ≤ 2*h^(n+1)*D/(n.factorial : ℝ) := by
  have hmem (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) : a+h*w ∈ Icc a (a+h) := by
    constructor <;> nlinarith [mul_nonneg hh.le hw.1,
      mul_le_mul_of_nonneg_left hw.2 hh.le]
  have hmass : (gaussValueRow n a h u v κ).mass ≤ (a+h)-a := by
    have hκ := (intervalIntegrable_iff.mp hi).aestronglyMeasurable
    have hκb : ∀ᵐ y ∂volume.restrict (uIoc (a+h*u) (a+h*v)), |κ y| ≤ 1 := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with y hy
      exact hk y ⟨le_of_lt hy.1, hy.2⟩
    simpa [ValueRow.mass, gaussValueRow] using GaussLegendre.sum_abs_partialRow_le_length
      n (by omega) a h u v hh hu hv κ hκ hκb
  have h := (gaussValueRow n a h u v κ).norm_defect_le hn hD0 (hmem u hu) (hmem v hv)
    (fun i => (GaussLegendre.cellNode_mem_Ioo n a h hh i).1.le
      |> fun hlo => ⟨hlo, (GaussLegendre.cellNode_mem_Ioo n a h hh i).2.le⟩)
    hk hi hmass (partialRow_monomial_exactness n a h u v hh κ hi) hf hD
  simpa [gaussValueRow, ValueRow.evaluate] using h

theorem sum_partialRow_one (m : ℕ) (hm : 1 ≤ m) (a h u v : ℝ) (hh : 0 < h) :
    (∑ j : Fin m, GaussLegendre.partialRow m a h u v (fun _ => 1) j) =
      (a+h*v)-(a+h*u) := by
  have hx := partialRow_monomial_exactness m a h u v hh (fun _ => 1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume _ _) 0 hm
  simpa [gaussValueRow] using hx.symm

theorem sum_centerRow (m : ℕ) (hm : 1 ≤ m) (a : ℝ) :
    (∑ b : Fin m, centerRow a b) = a := by
  simpa [centerRow] using sum_partialRow_one m hm 0 1 0 a (by norm_num)

theorem norm_centerRow_defect_le (m : ℕ) (hm : 1 ≤ m)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (f : ℝ → E) (D : ℝ) (hD0 : 0 ≤ D)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ m f t)
    (hD : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDeriv m f t‖ ≤ D) :
    ‖(∫ t in 0..a, f t) - ∑ b : Fin m, centerRow a b • f (centerNode b)‖ ≤
      2*D/(m.factorial:ℝ) := by
  simpa [centerRow, centerNode] using norm_partialRow_defect_le m hm 0 1 0 a
    (by norm_num) (by norm_num) ha (fun _ => 1) intervalIntegrable_const
    (by intro y hy; norm_num) f D hD0 (by simpa using hf) (by simpa using hD)


/-- The actual full unit-cell GL output row has the same sharp value defect. -/
theorem norm_gaussWeight_defect_le (m : ℕ) (hm : 1 ≤ m)
    (f : ℝ → E) (D : ℝ) (hD0 : 0 ≤ D)
    (hf : ∀ t ∈ Icc (0:ℝ) 1, ContDiffAt ℝ m f t)
    (hD : ∀ t ∈ Icc (0:ℝ) 1, ‖iteratedDeriv m f t‖ ≤ D) :
    ‖(∫ t in 0..1, f t) - ∑ b : Fin m, GaussLegendre.weight m b • f (centerNode b)‖ ≤
      2*D/(m.factorial:ℝ) := by
  have hc (b : Fin m) : centerRow 1 b = GaussLegendre.weight m b := by
    rw [centerRow, GaussLegendre.partialRow_full_one m 0 1 (by norm_num)]
    simp [GaussLegendre.cellWeight]
  simpa only [hc] using norm_centerRow_defect_le m hm 1 (by norm_num) f D hD0 hf hD

/-- Every point of a finite interval partition lies in an actual closed cell. -/
theorem exists_cell_mem {lo hi : ℝ} (M : IntervalMesh lo hi) (t : ℝ)
    (ht : t ∈ Icc lo hi) : ∃ c : M.Cell, t ∈ Icc (M.left c) (M.right c) := by
  classical
  by_cases he : t = lo
  · refine ⟨0, ?_⟩
    subst t
    have hl : M.left 0 = lo := by simp [IntervalMesh.left, M.first]
    exact ⟨hl.le, hl.ge.trans (sub_pos.mp (M.length_pos 0)).le⟩
  have hex : ∃ i, t ≤ M.point i := ⟨Fin.last _, by simpa [M.last] using ht.2⟩
  let k := Fin.find (fun i => t ≤ M.point i) hex
  have hk : t ≤ M.point k := Fin.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hz
    have htl : t ≤ lo := by simpa [hz, M.first] using hk
    exact he (le_antisymm htl ht.1)
  obtain ⟨c, hc⟩ := Fin.exists_succ_eq_of_ne_zero hk0
  refine ⟨c, ?_, ?_⟩
  · have hlt : c.castSucc < k := by rw [← hc]; exact c.castSucc_lt_succ
    exact (lt_of_not_ge (Fin.find_min hex hlt)).le
  · simpa [IntervalMesh.right, hc] using hk

omit [CompleteSpace E] in
theorem cellRegularity_continuousOn {lo hi : ℝ} (M : IntervalMesh lo hi)
    (m : ℕ) (f : ℝ → E) (D : M.Cell → ℝ) (hf : CellRegularity M m f D) :
    ContinuousOn f (Icc lo hi) := by
  intro t ht
  obtain ⟨c, hc⟩ := exists_cell_mem M t ht
  exact (hf.2.1 c t hc).continuousAt.continuousWithinAt

omit [CompleteSpace E] [NormedSpace ℝ E] in
private theorem mesh_sum_sub {lo hi : ℝ} (M : IntervalMesh lo hi) (F : ℝ → E) :
    (∑ c : M.Cell, (F (M.right c) - F (M.left c))) = F hi - F lo := by
  have hs := (Fin.sum_univ_succ (fun i => F (M.point i))).symm.trans
    (Fin.sum_univ_castSucc (fun i => F (M.point i)))
  simp only [M.first, M.last] at hs
  rw [Finset.sum_sub_distrib]
  change (∑ c : M.Cell, F (M.point c.succ)) - (∑ c : M.Cell, F (M.point c.castSucc)) = _
  calc
    _ = (F lo + ∑ c : M.Cell, F (M.point c.succ)) -
        (F lo + ∑ c : M.Cell, F (M.point c.castSucc)) := by abel
    _ = ((∑ c : M.Cell, F (M.point c.castSucc)) + F hi) -
        (F lo + ∑ c : M.Cell, F (M.point c.castSucc)) := by rw [hs]
    _ = _ := by abel

omit [CompleteSpace E] in
/-- Clipped cumulative cell integrals telescope exactly, before taking norms. -/
theorem sum_integral_clipped_left {lo hi : ℝ} (M : IntervalMesh lo hi)
    (f : ℝ → E) (hf : ContinuousOn f (Icc lo hi)) (t : ℝ) (ht : t ∈ Icc lo hi) :
    (∑ c : M.Cell, ∫ x in M.left c..M.clipped t c, f x) = ∫ x in lo..t, f x := by
  let P : ℝ → E := fun x => ∫ z in lo..x, f z
  have hInt (x : ℝ) (hx : x ∈ Icc lo hi) : IntervalIntegrable f volume lo x :=
    ContinuousOn.intervalIntegrable_of_Icc hx.1 (hf.mono (by
      intro z hz; exact ⟨hz.1, hz.2.trans hx.2⟩))
  have hcell (c : M.Cell) : (∫ x in M.left c..M.clipped t c, f x) =
      P (min t (M.right c)) - P (min t (M.left c)) := by
    by_cases h : t ≤ M.left c
    · simp [IntervalMesh.clipped, min_eq_left h,
        min_eq_left (h.trans (sub_pos.mp (M.length_pos c)).le), max_eq_left h]
    · have hl : M.left c ≤ t := (lt_of_not_ge h).le
      have hlr : M.left c ≤ M.right c := (sub_pos.mp (M.length_pos c)).le
      rw [IntervalMesh.clipped, max_eq_right (le_min hl hlr), min_eq_right hl]
      exact (intervalIntegral.integral_interval_sub_left
        (hInt _ ⟨le_min ht.1 ((M.lo_le_left c).trans hlr),
          (min_le_right _ _).trans (M.right_le_hi c)⟩)
        (hInt _ ⟨M.lo_le_left c, hlr.trans (M.right_le_hi c)⟩)).symm
  simp_rw [hcell]
  rw [mesh_sum_sub M (fun x => P (min t x))]
  simp [P, min_eq_left ht.2, min_eq_right ht.1]

omit [CompleteSpace E] in
/-- Signed clipped cell integrals reproduce the entire oriented interval. -/
theorem sum_integral_clipped {lo hi : ℝ} (M : IntervalMesh lo hi)
    (f : ℝ → E) (hf : ContinuousOn f (Icc lo hi)) (u v : ℝ)
    (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo hi) :
    (∑ c : M.Cell, ∫ x in M.clipped u c..M.clipped v c, f x) =
      ∫ x in u..v, f x := by
  have hInt (c : M.Cell) (t : ℝ) :
      IntervalIntegrable f volume (M.left c) (M.clipped t c) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (M.clipped_mem t c).1
    apply hf.mono
    intro x hx
    exact ⟨(M.lo_le_left c).trans hx.1,
      (hx.2.trans (M.clipped_mem t c).2).trans (M.right_le_hi c)⟩
  simp_rw [← intervalIntegral.integral_interval_sub_left (hInt _ v) (hInt _ u)]
  rw [Finset.sum_sub_distrib, sum_integral_clipped_left M f hf v hv,
    sum_integral_clipped_left M f hf u hu]
  apply intervalIntegral.integral_interval_sub_left
  · exact ContinuousOn.intervalIntegrable_of_Icc hv.1 (hf.mono (by
      intro x hx; exact ⟨hx.1, hx.2.trans hv.2⟩))
  · exact ContinuousOn.intervalIntegrable_of_Icc hu.1 (hf.mono (by
      intro x hx; exact ⟨hx.1, hx.2.trans hu.2⟩))


/-- Actual signed interval-row weights reproduce constants exactly. -/
theorem sum_intervalRow {lo hi : ℝ} (M : IntervalMesh lo hi) (m : ℕ) (hm : 1 ≤ m)
    (u v : ℝ) (hu : u ∈ Icc lo hi) (hv : v ∈ Icc lo hi) :
    (∑ j : M.Source m, M.row m u v j) = v-u := by
  have hsum : (∑ c : M.Cell, (M.clipped v c - M.clipped u c)) = v-u := by
    simpa using sum_integral_clipped M (fun _ : ℝ => (1:ℝ)) continuousOn_const u v hu hv
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ c : M.Cell, (M.clipped v c - M.clipped u c) := by
      apply Finset.sum_congr rfl
      intro c _
      simp_rw [M.row_eq_partialRow]
      rw [sum_partialRow_one m hm _ _ _ _ (M.length_pos c),
        M.left_add_length_mul_normalizedCoordinate,
        M.left_add_length_mul_normalizedCoordinate]
    _ = _ := hsum

/-- The actual mesh row obtains the exact sum of the approved cell budgets.
The signed cell integrals telescope before norms; no cumulative-row factor is lost. -/
theorem intervalRowDefect : IntervalRowDefectStatement (E := E) := by
  intro lo hi M m hm u v hu hv f D hreg
  have hcell (c : M.Cell) :
      ‖(∫ t in M.clipped u c..M.clipped v c, f t) -
        ∑ j : Fin m, M.row m u v (c,j) • f (M.location m (c,j))‖ ≤
        2 * M.length c ^ (m+1) * D c / (m.factorial:ℝ) := by
    have hf : ∀ t ∈ Icc (M.left c) (M.left c + M.length c),
        ContDiffAt ℝ m f t := by simpa [IntervalMesh.length] using hreg.2.1 c
    have hD : ∀ t ∈ Icc (M.left c) (M.left c + M.length c),
        ‖iteratedDeriv m f t‖ ≤ D c := by simpa [IntervalMesh.length] using hreg.2.2 c
    have h := norm_partialRow_defect_le m hm (M.left c) (M.length c)
      (M.normalizedCoordinate u c) (M.normalizedCoordinate v c) (M.length_pos c)
      (M.normalizedCoordinate_mem u c) (M.normalizedCoordinate_mem v c)
      (fun _ => 1) intervalIntegrable_const (by intro y hy; norm_num) f (D c)
      (hreg.1 c) hf hD
    simpa only [one_smul, M.left_add_length_mul_normalizedCoordinate,
      M.row_eq_partialRow, IntervalMesh.location] using h
  change ‖(∫ t in u..v, f t) - ∑ j : M.Source m,
    M.row m u v j • f (M.location m j)‖ ≤ _
  rw [Fintype.sum_prod_type, ← sum_integral_clipped M f
    (cellRegularity_continuousOn M m f D hreg) u v hu hv,
    ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun c _ => hcell c))

end AcceleratedLogConcave.Numerics.AffineResidual
end AffineQuadratureRows

noncomputable section AffineQuadratureAngleKernel
/-!
Concrete derivative and singular quadrature adapters for the frozen residual interface.
The GL cell and Option-origin arguments adapt the published W09 singular review
bridges, without importing those audit modules.
-/
open MeasureTheory Set Polynomial
open scoped BigOperators ContDiff
open AcceleratedLogConcave.Numerics
open AcceleratedLogConcave.Numerics.AffineGraph
open AcceleratedLogConcave.Numerics.AffineGraph.MeanGeometry
open AcceleratedLogConcave.Numerics.GaussLegendre
open AcceleratedLogConcave.Numerics.SingularKernel
open AcceleratedLogConcave.Numerics.ReciprocalQuadrature
set_option autoImplicit false

namespace AcceleratedLogConcave.Numerics.AffineResidual
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual derivative row reproduces the derivative at zero of every
Taylor monomial below its interpolation order. -/
private theorem derivativeRow_pow_zero (m k : ℕ) (hk : k < m)
    (ψ : ℝ) (hψ : 0 < ψ) :
    (∑ j : Fin m, derivativeRow m 0 ψ 0 j * (cellNode m 0 ψ j)^k) =
      if k = 1 then (1:ℝ) else 0 := by
  have hp : (X^k : ℝ[X]).degree < m := by
    rw [degree_pow, degree_X]
    simpa using hk
  have h := derivativeRow_reproduces m 0 ψ 0 hψ (X^k) hp
  simp only [eval_pow, eval_X] at h
  rw [←h]
  by_cases hk0 : k = 0
  · simp [hk0]
  by_cases hk1 : k = 1
  · simp [hk1]
  simp [derivative_X_pow, hk1, show k-1 ≠ 0 by omega]

omit [CompleteSpace E] in
private theorem derivativeRow_taylor_zero (m : ℕ) (hm : 2 ≤ m)
    (ψ : ℝ) (hψ : 0 < ψ) (f : ℝ → E) :
    (∑ j : Fin m, derivativeRow m 0 ψ 0 j •
      taylorPolynomial f m 0 (cellNode m 0 ψ j)) = deriv f 0 := by
  unfold taylorPolynomial
  simp_rw [sub_zero, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  calc
    _ = ∑ k ∈ Finset.range m, (if k = 1 then (1:ℝ) else 0) •
        iteratedDeriv k f 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [←Finset.sum_smul]
      simp_rw [←mul_div_assoc]
      rw [←Finset.sum_div, derivativeRow_pow_zero m k (Finset.mem_range.mp hk) ψ hψ]
      by_cases hk1 : k = 1 <;> simp [hk1]
    _ = deriv f 0 := by simp [show 1 < m by omega, iteratedDeriv_one]

/-- The angle defect carries exactly one reciprocal-angle factor from the
physical derivative row, leaving the source power `ψ^(m-1)`. -/
theorem angleDerivativeDefect : AngleDerivativeDefectStatement (E := E) := by
  intro m hm ψ D hψ hD f hf hbound
  have hTaylor := derivativeRow_taylor_zero m hm ψ hψ f
  have hrem (j : Fin m) :
      ‖f (cellNode m 0 ψ j) - taylorPolynomial f m 0 (cellNode m 0 ψ j)‖ ≤
        D * ψ^m / (m.factorial:ℝ) := by
    have hn := cellNode_mem_Ioo m 0 ψ hψ j
    have hnj : cellNode m 0 ψ j ∈ Icc (0:ℝ) ψ := by
      simpa using And.intro hn.1.le hn.2.le
    apply (norm_sub_taylorPolynomial_le (by omega : 1 ≤ m) hnj hf hbound).trans
    simp only [sub_zero]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnj.1 hnj.2 m) hD)
      (Nat.cast_nonneg _)
  have hmass := sum_abs_derivativeRow_le m 0 ψ 0 hψ
    (show (0:ℝ) ∈ Icc 0 (0+ψ) from ⟨le_rfl, by linarith⟩)
  calc
    ‖deriv f 0 - ∑ j : Fin m, derivativeRow m 0 ψ 0 j • f (cellNode m 0 ψ j)‖ =
        ‖∑ j : Fin m, derivativeRow m 0 ψ 0 j •
          (f (cellNode m 0 ψ j) - taylorPolynomial f m 0 (cellNode m 0 ψ j))‖ := by
      rw [norm_sub_rev, ←hTaylor, ←Finset.sum_sub_distrib]
      simp only [smul_sub]
    _ ≤ ∑ j : Fin m, |derivativeRow m 0 ψ 0 j| *
        ‖f (cellNode m 0 ψ j) - taylorPolynomial f m 0 (cellNode m 0 ψ j)‖ := by
      simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le
        (s := Finset.univ) (f := fun j : Fin m => derivativeRow m 0 ψ 0 j •
          (f (cellNode m 0 ψ j) - taylorPolynomial f m 0 (cellNode m 0 ψ j)))
    _ ≤ ∑ j : Fin m, |derivativeRow m 0 ψ 0 j| * (D * ψ^m / (m.factorial:ℝ)) := by
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hrem j) (abs_nonneg _))
    _ = (∑ j : Fin m, |derivativeRow m 0 ψ 0 j|) *
        (D * ψ^m / (m.factorial:ℝ)) := by rw [Finset.sum_mul]
    _ ≤ ((m:ℝ)^3 / ψ) * (D * ψ^m / (m.factorial:ℝ)) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = (m:ℝ)^3 * ψ^(m-1) * D / (m.factorial:ℝ) := by
      have hexp : m = (m-1)+1 := by omega
      have hpow := pow_succ ψ (m-1)
      rw [←hexp] at hpow
      rw [hpow]
      field_simp

private def kernelGaussRow (m : ℕ) (a c : ℝ) : ValueRow (Fin m) where
  node := cellNode m a (c-a)
  weight := cellWeight m (c-a)
  start := a
  finish := c

private theorem kernelGaussRow_exact (m : ℕ) {a c : ℝ} (hac : a<c) :
    (kernelGaussRow m a c).Exact (fun _ => 1) a m := by
  intro k hk
  have hp1 : ((X-C a)^k : ℝ[X]).degree < m := by
    rw [degree_pow, degree_X_sub_C]
    simpa using hk
  have hp : ((X-C a)^k : ℝ[X]).degree < (2*m : ℕ) :=
    hp1.trans_le (by exact_mod_cast (show m ≤ 2*m by omega))
  simpa [kernelGaussRow] using
    integral_cell_eq_sum m a (c-a) (sub_pos.mpr hac) ((X-C a)^k) hp

private theorem kernelGaussRow_mass (m : ℕ) (hm : 1≤m) {a c : ℝ} (hac : a<c) :
    (kernelGaussRow m a c).mass = c-a := by
  simp only [ValueRow.mass, kernelGaussRow]
  simp_rw [abs_of_nonneg (cellWeight_nonneg m _ _ (sub_nonneg.mpr hac.le))]
  exact sum_cellWeight m (by omega) (c-a)

omit [CompleteSpace E] in
/-- The coefficient at `none` is retained; it is precisely the origin subtraction
required by the regularized singular kernel value rule. -/
theorem actualKernel_inventory {m : ℕ} (G : MeanGeometry m) (f : ℝ → E) :
    (∑ ρ : G.Kernel, G.kernelCoeff ρ • f (G.rho ρ)) =
      kernelValueRule f (backwardEnd G.R) (G.backward.location m)
        (fun z => cellWeight m (G.backward.length z.1) z.2) := by
  have h (k : ℕ) (mesh : Fin (k+2) → ℝ) :
      (∑ z, kernelValueCoefficient m mesh z • f (kernelValueLocation m mesh z)) =
        kernelValueRule f (meshHorizon mesh)
          (fun z : Fin (k+1) × Fin m =>
            cellNode m (meshCellLeft mesh z.1) (meshCellLength mesh z.1) z.2)
          (fun z => cellWeight m (meshCellLength mesh z.1) z.2) := by
    rw [Fintype.sum_option]
    simp only [kernelValueCoefficient, kernelValueLocation, kernelValueRule,
      kernelNodeCoefficient, smul_sub, Finset.sum_sub_distrib,
      sub_smul, neg_div, one_div, neg_smul, Finset.sum_smul]
    abel
  have he := h G.backward.cellsPred G.backward.point
  have hlast : meshHorizon G.backward.point = backwardEnd G.R := G.backward.last
  rw [hlast] at he
  exact he

/-- Actual singular quadrature, including the origin coefficient and both
endpoint conditions. No residual estimate is a hypothesis. -/
theorem kernelDefect : KernelDefectStatement (E := E) := by
  intro m G hm l u A h₀ hl hu hA hh hgeom f hf hf0 hfb hD
  rw [actualKernel_inventory]
  have hp := G.backward.strictMono
  have h := norm_kernel_value_defect_le m hm hl G.backwardEnd_pos
    G.backwardEnd_lt_one hu hA hh hf hf0 hfb hD
    G.backward.point hp G.backward.first G.backward.last
    (fun c => kernelGaussRow m (G.backward.left c) (G.backward.right c))
    (fun _ => rfl) (fun _ => rfl)
    (fun c j => by
      exact ⟨(G.backward.location_mem_cell m (c,j)).1.le,
        (G.backward.location_mem_cell m (c,j)).2.le⟩)
    (fun c j => (G.backward.location_mem_interval m (c,j)).1)
    (fun c => (kernelGaussRow_mass m hm (hp c.castSucc_lt_succ)).le)
    (fun c => kernelGaussRow_exact m (hp c.castSucc_lt_succ)) hgeom
  exact h

end AcceleratedLogConcave.Numerics.AffineResidual
end AffineQuadratureAngleKernel
