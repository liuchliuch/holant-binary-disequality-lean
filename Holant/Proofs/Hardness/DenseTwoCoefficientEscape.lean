import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Complex scalar escape for the dense two-coefficient
branch. The only map considered is r↦r/(2r+1). This file proves no graph,
interpolation programme, arbitrary six-coefficient classification or codec
transport. The local graph/table construction belongs to its separate caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseTwoCoefficientEscape

def RootOfUnity (r : ℂ) : Prop := ∃ n : ℕ,0<n ∧ r^n=1
def InfiniteOrder (r : ℂ) : Prop := ∀ n : ℕ,0<n → r^n≠1

def step (r : ℂ) : ℂ := r/(2*r+1)

theorem infinite_iff_not_root (r : ℂ) : InfiniteOrder r ↔ ¬RootOfUnity r := by
  simp only [InfiniteOrder,RootOfUnity,not_exists,not_and]

theorem root_norm {r : ℂ} (h : RootOfUnity r) : ‖r‖=1 := by
  obtain ⟨n,hn,hp⟩ := h
  have hnorm : ‖r‖^n=1 := by simpa only [norm_pow,norm_one] using congrArg norm hp
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg r) (Nat.ne_of_gt hn)).mp hnorm

theorem infinite_of_norm_ne_one {r : ℂ} (h : ‖r‖≠1) : InfiniteOrder r :=
  (infinite_iff_not_root r).mpr (fun hr=>h (root_norm hr))

/-- A unit-circle point never makes this denominator zero. -/
theorem denominator_nonzero {r : ℂ} (hr : ‖r‖=1) : 2*r+1≠0 := by
  intro h
  have he : (2 : ℂ)*r=-1 := eq_neg_of_add_eq_zero_left h
  have hn := congrArg norm he
  norm_num [norm_mul,hr] at hn

/-- The two unit-circle conditions force their unique intersection r=-1. -/
theorem unit_norms_force_neg_one {r : ℂ} (hr : ‖r‖=1) (hs : ‖step r‖=1) : r=-1 := by
  have hd : ‖2*r+1‖=1 := by
    simpa only [step,norm_div,hr,one_div,inv_eq_one] using hs
  have h1 : r.re*r.re+r.im*r.im=1 := by
    simpa only [Complex.normSq_apply,hr,one_pow] using Complex.normSq_eq_norm_sq r
  have h2 : (2*r.re+1)*(2*r.re+1)+(2*r.im)*(2*r.im)=1 := by
    have h := Complex.normSq_eq_norm_sq ((2 : ℂ)*r+1)
    rw [hd] at h
    simpa [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im] using h
  have hre : r.re=-1 := by nlinarith
  have him : r.im=0 := by
    apply mul_self_eq_zero.mp
    nlinarith
  apply Complex.ext <;> simp [hre,him]

/-- In particular, two root-of-unity ratios force r=-1. The first root
condition already implies r≠0, so no redundant nonzero premise is needed. -/
theorem two_roots_force_neg_one {r : ℂ} (hr : RootOfUnity r) (hs : RootOfUnity (step r)) : r=-1 :=
  unit_norms_force_neg_one (root_norm hr) (root_norm hs)

theorem step_neg_one : step (-1)=1 := by norm_num [step]
theorem step_one : step 1=(1 : ℂ)/3 := by norm_num [step]
theorem second_step_neg_one : step (step (-1))=(1 : ℂ)/3 := by rw [step_neg_one,step_one]

theorem infinite_third : InfiniteOrder ((1 : ℂ)/3) := by
  apply infinite_of_norm_ne_one
  norm_num [norm_div]

theorem infinite_neg_half : InfiniteOrder ((-1 : ℂ)/2) := by
  apply infinite_of_norm_ne_one
  norm_num [norm_div]

theorem neg_one_denominators :
    (2 : ℂ)*(-1)+1≠0 ∧ (2 : ℂ)*step (-1)+1≠0 := by
  rw [step_neg_one]
  norm_num

/-- The unit-circle branch outside -1 escapes after ONE valid step. -/
theorem one_step_escape {r : ℂ} (hr : ‖r‖=1) (hne : r≠-1) :
    2*r+1≠0 ∧ InfiniteOrder (step r) := by
  refine ⟨denominator_nonzero hr,infinite_of_norm_ne_one ?_⟩
  intro hs
  exact hne (unit_norms_force_neg_one hr hs)

/-- At most two valid steps suffice. Both denominator certificates are
constructed; no successful division or infinite-order branch is supplied. -/
theorem escape (r : ℂ) :
    InfiniteOrder r ∨
      (2*r+1≠0 ∧ InfiniteOrder (step r)) ∨
      (r=-1 ∧ 2*r+1≠0 ∧ 2*step r+1≠0 ∧
        step r=1 ∧ step (step r)=(1 : ℂ)/3 ∧ InfiniteOrder (step (step r))) := by
  by_cases hr : ‖r‖=1
  · by_cases he : r=-1
    · subst r
      refine Or.inr (Or.inr ⟨rfl,neg_one_denominators.1,neg_one_denominators.2,
        step_neg_one,second_step_neg_one,?_⟩)
      rw [second_step_neg_one]
      exact infinite_third
    · exact Or.inr (Or.inl (one_step_escape hr he))
  · exact Or.inl (infinite_of_norm_ne_one hr)

theorem step_nonzero {r : ℂ} (hr : r≠0) (hd : 2*r+1≠0) : step r≠0 :=
  div_ne_zero hr hd

/-- A concrete finite selector; its choice depends only on the original ratio.
It does not search for, or accept, a successful interpolation certificate. -/
noncomputable def depth (r : ℂ) : Fin 3 := by
  classical
  exact if ‖r‖=1 then (if r=-1 then 2 else 1) else 0

abbrev selectedRatio (r : ℂ) : ℂ := (step^[(depth r).val]) r

theorem depth_lt_three (r : ℂ) : (depth r).val<3 := (depth r).isLt

/-- Every actually executed denominator is nonzero. Original r≠0 is kept
explicit, since 0 satisfies InfiniteOrder but its geometric nodes coincide. -/
theorem depth_spec (r : ℂ) (hr : r≠0) :
    (∀ i : ℕ,i<(depth r).val → 2*(step^[i]) r+1≠0) ∧
      selectedRatio r≠0 ∧ InfiniteOrder (selectedRatio r) := by
  classical
  unfold selectedRatio
  by_cases hn : ‖r‖=1
  · by_cases he : r=-1
    · subst r
      have hd : depth (-1)=(2 : Fin 3) := by simp [depth]
      rw [hd]
      refine ⟨?_,?_,?_⟩
      · intro i hi
        change i<2 at hi
        interval_cases i <;> norm_num [Function.iterate_succ_apply,step]
      · norm_num [Function.iterate_succ_apply,step]
      · simpa [Function.iterate_succ_apply,step_neg_one,step_one] using infinite_third
    · have hd : depth r=(1 : Fin 3) := by simp [depth,hn,he]
      rw [hd]
      obtain ⟨hden,hinf⟩ := one_step_escape hn he
      refine ⟨?_,?_,?_⟩
      · intro i hi
        have hz : i=0 := by omega
        subst i
        exact hden
      · exact step_nonzero hr hden
      · exact hinf
  · have hd : depth r=(0 : Fin 3) := by simp [depth,hn]
    rw [hd]
    refine ⟨?_,hr,infinite_of_norm_ne_one hn⟩
    intro i hi
    omega

theorem selected_nonzero (r : ℂ) (hr : r≠0) : selectedRatio r≠0 := (depth_spec r hr).2.1
theorem selected_infinite (r : ℂ) (hr : r≠0) : InfiniteOrder (selectedRatio r) := (depth_spec r hr).2.2
theorem executed_denominator (r : ℂ) (hr : r≠0) (i : ℕ) (hi : i<(depth r).val) :
    2*(step^[i]) r+1≠0 := (depth_spec r hr).1 i hi

/-- Nonzero is indispensable here; InfiniteOrder alone deliberately does not
exclude zero. This elementary cancellation proves distinct actual powers. -/
theorem powers_injective {z : ℂ} (hz : z≠0) (hi : InfiniteOrder z) :
    Function.Injective (fun n : ℕ=>z^n) := by
  have hle (a b : ℕ) (hab : a≤b) (he : z^a=z^b) : a=b := by
    by_contra hne
    have hpos : 0<b-a := by omega
    have heq : a+(b-a)=b := by omega
    have hp : z^a*z^(b-a)=z^a*1 := by rw [←pow_add,heq,mul_one,he]
    exact (hi (b-a) hpos) ((mul_left_cancel₀ (pow_ne_zero a hz)) hp)
  intro a b he
  rcases le_total a b with hab|hba
  · exact hle a b hab he
  · exact (hle b a hba he.symm).symm

/-- Directly usable interpolation-node separation, derived from the finite
selector and original ratio nonzero rather than supplied by its caller. -/
theorem selected_nodes_injective (r : ℂ) (hr : r≠0) (m : ℕ) :
    Function.Injective (fun i : Fin (m+1)=>selectedRatio r^(i.val+1)) := by
  intro i j he
  apply Fin.ext
  exact Nat.add_right_cancel (powers_injective (selected_nonzero r hr) (selected_infinite r hr) he)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.DenseTwoCoefficientEscape
