import AcceleratedLogConcave.Tensor.MaterialWordExpansion

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
open Analysis.OrderedJacobianWords

/-- One explicit source-compatible base shared by every allocated order. -/
def materialWordMassBase (m : ℕ) : ℝ := 27*((m:ℝ)+1)^2

theorem materialWordMassBase_one_le (m : ℕ) : 1 ≤ materialWordMassBase m := by
  unfold materialWordMassBase
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem materialCoefficientTerms_mass_uniform (l : ℝ) (hl : |l| ≤ 1)
    (k m : ℕ) (hkm : k ≤ m) :
    materialMass (materialCoefficientTerms l k) ≤ (materialWordMassBase m)^(k+1) := by
  let B := materialWordMassBase m
  have hB : 1 ≤ B := materialWordMassBase_one_le m
  have hjet (n : ℕ) (hn : n ≤ k) :
      materialMass (materialIterate l (.coefficient (Sum.inl 0)) n) ≤ B^k := by
    have hn' : (n:ℝ) ≤ m := by exact_mod_cast hn.trans hkm
    have hC : 3*((2:ℝ)+3*(n:ℝ)+1)^2 ≤ B := by
      dsimp [B,materialWordMassBase]
      have hs : ((n:ℝ)+1)^2 ≤ ((m:ℝ)+1)^2 :=
        (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
      nlinarith
    exact (materialIterate_mass l hl (.coefficient (Sum.inl 0)) n).trans
      ((materialMassBudget_le 2 n).trans
        ((pow_le_pow_left₀ (by positivity) hC n).trans (pow_le_pow_right₀ hB hn)))
  rw [materialCoefficientTerms_mass]
  calc
    _ ≤ B^k+(k:ℝ)*B^k := add_le_add (hjet k le_rfl)
      (mul_le_mul_of_nonneg_left (hjet (k-1) (Nat.sub_le _ _)) (Nat.cast_nonneg k))
    _ = ((k:ℝ)+1)*B^k := by ring
    _ ≤ B*B^k := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
      have hk' : (k:ℝ) ≤ m := by exact_mod_cast hkm
      dsimp [B,materialWordMassBase]
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    _ = B^(k+1) := by rw [pow_succ]; ring

theorem materialWordTerms_mass_uniform (l : ℝ) (hl : |l| ≤ 1)
    (w : Word) (m : ℕ) (hwm : order w ≤ m) :
    materialMass (materialWordTerms l w) ≤ (materialWordMassBase m)^(order w) := by
  induction w with
  | nil => simp [materialWordTerms,materialMass]
  | cons j w ih =>
    cases w with
    | nil =>
      simpa [materialWordTerms,order_cons,order_nil] using
        materialCoefficientTerms_mass_uniform l hl j m (by simp only [order_cons,order_nil] at hwm; omega)
    | cons k w =>
      have hjm : j ≤ m := by simp only [order_cons] at hwm; omega
      have htail : order (k::w) ≤ m := by rw [order_cons] at hwm; omega
      rw [materialWordTerms,materialTermsProduct_mass]
      have hh := mul_le_mul (materialCoefficientTerms_mass_uniform l hl j m hjm)
        (ih htail) (materialMass_nonneg _)
        (pow_nonneg ((materialWordMassBase_one_le m).trans' (by norm_num)) _)
      exact hh.trans_eq (by simp only [←pow_add,order_cons])

theorem materialWords_total_mass (l : ℝ) (hl : |l| ≤ 1) (m : ℕ) :
    ((words m).map (fun w => materialMass (materialWordTerms l w))).sum ≤
      (m.factorial:ℝ)*(materialWordMassBase m)^m := by
  have hterm (w : Word) (hw : w ∈ words m) :
      materialMass (materialWordTerms l w) ≤ (materialWordMassBase m)^m := by
    have hh := materialWordTerms_mass_uniform l hl w m (order_of_mem_words hw).le
    simpa only [order_of_mem_words hw] using hh
  have hc (ws : List Word) (c : ℝ) : (ws.map (fun _ => c)).sum = (ws.length:ℝ)*c := by
    induction ws with
    | nil => simp
    | cons w ws ih => simp [add_mul]; ring
  calc
    _ ≤ ((words m).map (fun _ => (materialWordMassBase m)^m)).sum := List.sum_le_sum hterm
    _ = ((words m).length:ℝ)*(materialWordMassBase m)^m := hc _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast coefficient_mass_le_factorial m)
      (pow_nonneg (by linarith [materialWordMassBase_one_le m]) _)

theorem materialWords_physical_mass (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (m : ℕ) (hm : 0<m) :
    ((words m).map (fun w => l^w.length * materialMass (materialWordTerms l w))).sum ≤
      l*(m.factorial:ℝ)*(materialWordMassBase m)^m := by
  have hterm (w : Word) (hw : w ∈ words m) :
      l^w.length * materialMass (materialWordTerms l w) ≤
      l*materialMass (materialWordTerms l w) := by
    have hlen : 1 ≤ w.length := List.length_pos_iff.mpr (nonempty_of_mem_words hm hw)
    have hp : l^w.length ≤ l := by simpa using pow_le_pow_of_le_one hl0 hl1 hlen
    exact mul_le_mul_of_nonneg_right hp (materialMass_nonneg _)
  calc
    _ ≤ ((words m).map (fun w => l*materialMass (materialWordTerms l w))).sum := List.sum_le_sum hterm
    _ = l*((words m).map (fun w => materialMass (materialWordTerms l w))).sum := List.sum_map_mul_left _ _ _
    _ ≤ l*((m.factorial:ℝ)*(materialWordMassBase m)^m) :=
      mul_le_mul_of_nonneg_left (materialWords_total_mass l (by rwa [abs_of_nonneg hl0]) m) hl0
    _ = _ := by ring

end AcceleratedLogConcave.Tensor.ActualCoefficientIntegrability
