import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Data.List.OfFn

/-!

-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Topology ContDiff
namespace AcceleratedLogConcave.Analysis.SpatialVariation

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Ordered directional derivatives, retaining repeated directions. -/
def along : List E → (E → V) → E → V
  | [], f => f
  | v :: J, f => fun y => fderiv ℝ (along J f) y v

theorem contDiff_along (J : List E) {f : E → V} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (along J f) := by
  induction J with
  | nil => exact hf
  | cons v J ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

/-- Exact compatibility with the literal iterated Frechet derivative.
No norm estimate and no direction permutation is part of this bridge. -/
theorem along_ofFn_eq_iteratedFDeriv {f : E → V} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∀ (m : Fin n → E) (y : E),
      along (List.ofFn m) f y = iteratedFDeriv ℝ n f y m := by
  induction n with
  | zero =>
    intro m y
    simp only [List.ofFn_zero, along, iteratedFDeriv_zero_apply]
  | succ n ih =>
    intro m y
    rw [List.ofFn_succ]
    change fderiv ℝ (along (List.ofFn (Fin.tail m)) f) y (m 0) = _
    have he : along (List.ofFn (Fin.tail m)) f =
        fun z => iteratedFDeriv ℝ n f z (Fin.tail m) :=
      funext (fun z => ih (Fin.tail m) z)
    rw [he]
    have hjet : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) :=
      hf.iteratedFDeriv_right (by simp)
    exact ((hjet.differentiable (by simp) y).iteratedFDeriv_succ_apply_left').symm

theorem along_id_at_least_two (v w : E) (J : List E) :
    along (v :: w :: J) (id : E → E) = fun _ => 0 := by
  induction J generalizing v w with
  | nil =>
    funext y
    simp only [along, fderiv_id, ContinuousLinearMap.id_apply, fderiv_const_apply, zero_apply]
  | cons u J ih =>
    change (fun y => fderiv ℝ (along (w :: u :: J) (id : E → E)) y v) = _
    rw [ih w u]
    funext y
    simp only [fderiv_const_apply, zero_apply]

theorem along_eventuallyEq {f g : E → V} {y : E}
    (h : f =ᶠ[𝓝 y] g) (J : List E) : along J f =ᶠ[𝓝 y] along J g := by
  induction J with
  | nil => exact h
  | cons v J ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun L : E →L[ℝ] V => L v) hz

/-- Constant directions commute for a genuinely smooth map. -/
theorem direction_comm {f : E → V} (hf : ContDiff ℝ ∞ f) (v w : E) :
    (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v) =
      (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) := by
  funext y
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hd := hdf.differentiable (by simp) y
  have hw := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w y)).fderiv
  have hv := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v y)).fderiv
  rw [hw, hv]
  simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply] using
    (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

/-- Move ONE fixed direction past the complete ordered spatial list.
The order internal to J is unchanged. -/
theorem direction_along (J : List E) {f : E → V} (hf : ContDiff ℝ ∞ f) (w : E) :
    (fun y => fderiv ℝ (along J f) y w) =
      along J (fun y => fderiv ℝ f y w) := by
  induction J with
  | nil => rfl
  | cons v J ih =>
    change (fun y => fderiv ℝ (fun z => fderiv ℝ (along J f) z v) y w) =
      (fun y => fderiv ℝ (along J (fun z => fderiv ℝ f z w)) y v)
    rw [direction_comm (contDiff_along J hf) w v, ih]

/-- Joint representative for the ordered initial-data derivatives. -/
def jointAlong (J : List E) (C : ℝ × E → V) : ℝ × E → V :=
  along (J.map (fun v => ((0 : ℝ), v))) C

theorem contDiff_jointAlong (J : List E) {C : ℝ × E → V}
    (hC : ContDiff ℝ ∞ C) : ContDiff ℝ ∞ (jointAlong J C) :=
  contDiff_along _ hC

theorem jointAlong_slice (J : List E) {C : ℝ × E → V}
    (hC : ContDiff ℝ ∞ C) (t : ℝ) :
    (fun y => jointAlong J C (t,y)) = along J (fun y => C (t,y)) := by
  induction J with
  | nil => rfl
  | cons v J ih =>
    funext y
    have hd := ((contDiff_jointAlong J hC).differentiable (by simp) (t,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id y))
    have he : fderiv ℝ (fun z => jointAlong J C (t,z)) y v =
        fderiv ℝ (jointAlong J C) (t,y) (0,v) :=
      congrArg (fun L : E →L[ℝ] V => L v) hd.fderiv
    change fderiv ℝ (jointAlong J C) (t,y) (0,v) =
      fderiv ℝ (along J (fun z => C (t,z))) y v
    rw [← he, ih]

/-- Arbitrary-order smooth derivative interchange. Only time is differentiated
on the left; the right side takes the ordered INITIAL-DATA derivatives of
the time derivative. This is not an iterated time/material jet. -/
theorem hasDerivAt_along_slice (J : List E) {C : ℝ × E → V}
    (hC : ContDiff ℝ ∞ C) (t : ℝ) (y : E) :
    HasDerivAt (fun s => along J (fun z => C (s,z)) y)
      (along J (fun z => fderiv ℝ C (t,z) (1,0)) y) t := by
  have htime := ((contDiff_jointAlong J hC).differentiable (by simp) (t,y)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have he : (fun s => along J (fun z => C (s,z)) y) =
      fun s => jointAlong J C (s,y) := by
    funext s
    exact (congrFun (jointAlong_slice J hC s) y).symm
  rw [he]
  change HasDerivAt (fun s => jointAlong J C (s,y))
    (fderiv ℝ (jointAlong J C) (t,y) (1,0)) t at htime
  have hc := congrFun
    (direction_along (J.map (fun v => ((0 : ℝ),v))) hC ((1 : ℝ),(0 : E))) (t,y)
  have hD : ContDiff ℝ ∞ (fun p : ℝ × E => fderiv ℝ C p (1,0)) :=
    (hC.fderiv_right (by simp)).clm_apply contDiff_const
  change fderiv ℝ (jointAlong J C) (t,y) (1,0) =
    jointAlong J (fun p => fderiv ℝ C p (1,0)) (t,y) at hc
  rw [hc, congrFun (jointAlong_slice J hD t) y] at htime
  exact htime

/-- Transfer arbitrary-order spatial variations through one smooth local
representative valid on the ENTIRE CLOSED time slab. The only differential
input is the zeroth-order ODE, not any higher variation or growth property.
The singleton slab is handled directly, without uniqueness of its derivative. -/
theorem along_variation_of_local_representative
    {Y R : ℝ → E → V} {C : ℝ × E → V} {b : ℝ} (hb : 0 ≤ b)
    (hC : ContDiff ℝ ∞ C) (y : E)
    (hCY : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1, C (s,z) = Y s z)
    (hODE : ∀ s ∈ Icc 0 b, ∀ z ∈ ball y 1,
      HasDerivWithinAt (fun u => Y u z) (R s z) (Icc 0 b) s)
    (J : List E) {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun s => along J (Y s) y)
      (along J (R t) y) (Icc 0 b) t := by
  by_cases hbpos : 0 < b
  · have hslice (s : ℝ) (hs : s ∈ Icc 0 b) :
        along J (fun z => C (s,z)) y = along J (Y s) y := by
      apply (along_eventuallyEq (J := J) ?_).eq_of_nhds
      filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
      exact hCY s hs z hz
    have htime (z : E) (hz : z ∈ ball y 1) :
        fderiv ℝ C (t,z) (1,0) = R t z := by
      have hd := (hC.differentiable (by simp) (t,z)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
      have ha := (hODE t ht z hz).congr_of_mem (fun s hs => hCY s hs z hz) ht
      have hdw : HasDerivWithinAt (fun s => C (s,z))
          (fderiv ℝ C (t,z) (1,0)) (Icc 0 b) t := hd.hasDerivWithinAt
      exact (hdw.derivWithin (uniqueDiffOn_Icc hbpos t ht)).symm.trans
        (ha.derivWithin (uniqueDiffOn_Icc hbpos t ht))
    have hrhs : along J (fun z => fderiv ℝ C (t,z) (1,0)) y =
        along J (R t) y := by
      apply (along_eventuallyEq (J := J) ?_).eq_of_nhds
      filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0:ℝ) < 1)] with z hz
      exact htime z hz
    have h := (hasDerivAt_along_slice J hC t y).hasDerivWithinAt (s := Icc 0 b)
    rw [hrhs] at h
    exact h.congr_of_mem (fun s hs => (hslice s hs).symm) ht
  · have hbzero : b = 0 := le_antisymm (not_lt.mp hbpos) hb
    subst b
    have htzero : t = 0 := le_antisymm ht.2 ht.1
    subst t
    rw [Icc_self]
    exact HasFDerivWithinAt.singleton

/-- The first nontrivial top-order separation. The highest spatial variation
of Y occurs LINEARLY with coefficient Df(Y); the forcing contains only DY.
This is a genuine second-order chain-rule proof, not a definition of a
remainder obtained by subtracting the desired top-order term. -/
theorem second_composition_split {f Y : E → E}
    (hf : ContDiff ℝ ∞ f) (hY : ContDiff ℝ ∞ Y) (y v w : E) :
    along [v,w] (fun z => f (Y z)) y =
      fderiv ℝ f (Y y) (along [v,w] Y y) +
        (fderiv ℝ (fderiv ℝ f) (Y y) (fderiv ℝ Y y v)) (fderiv ℝ Y y w) := by
  have he : along [w] (fun z => f (Y z)) =
      fun z => (fderiv ℝ f (Y z)) (fderiv ℝ Y z w) := by
    funext z
    exact congrArg (fun L : E →L[ℝ] E => L w)
      (((hf.differentiable (by simp) (Y z)).hasFDerivAt.comp z
        (hY.differentiable (by simp) z).hasFDerivAt).fderiv)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdY : ContDiff ℝ ∞ (fderiv ℝ Y) := hY.fderiv_right (by simp)
  have hA := (hdf.differentiable (by simp) (Y y)).hasFDerivAt.comp y
    (hY.differentiable (by simp) y).hasFDerivAt
  have hB : DifferentiableAt ℝ (fun z => fderiv ℝ Y z w) y :=
    (hdY.clm_apply contDiff_const).differentiable (by simp) y
  have hd := (hA.clm_apply hB.hasFDerivAt).fderiv
  dsimp only [Function.comp_def] at hd
  change fderiv ℝ (along [w] (fun z => f (Y z))) y v = _
  rw [he, hd]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  rfl

end AcceleratedLogConcave.Analysis.SpatialVariation
