import Holant.Proofs.Hardness.ThreeModeAnnihilatorDifference
import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeRoots

/-! Collision-safe positive-moment interpolation. All copies of a desired root
are skipped by its annihilator and counted. Dividing by that positive
multiplicity makes a sum over the original, possibly repetitive root list exact. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeFilter
open scoped BigOperators
namespace D
export ThreeModeAnnihilator (differenceFilter differenceFilter_moments)
end D
variable {L : Type*} [Field L]
local instance : DecidableEq L := Classical.decEq L

def unwanted (roots : List L) (x : L) : List L := roots.filter fun r => decide (r≠x)
def multiplicity (roots : List L) (x : L) : ℕ := (roots.filter fun r => decide (r=x)).length

def denominator (roots : List L) (x : L) : L :=
  x*((unwanted roots x).map fun r=>x-r).prod

theorem denominator_ne_zero (roots : List L) (x : L) (hx : x≠0) : denominator roots x≠0 := by
  apply mul_ne_zero hx
  intro hz
  obtain ⟨r,hr,ha0⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp hz)
  have hr' : r≠x := of_decide_eq_true (List.mem_filter.mp hr).2
  exact hr' (sub_eq_zero.mp ha0).symm

theorem multiplicity_pos (roots : List L) (x : L) (hx : x∈roots) : 0<multiplicity roots x := by
  apply List.length_pos_iff.mpr
  intro he
  have h : x∈roots.filter (fun r=>decide (r=x)) := List.mem_filter.mpr ⟨hx,by simp⟩
  rw [he] at h
  exact List.not_mem_nil h

theorem unwanted_length (roots : List L) (x : L) (hx : x∈roots) :
    (unwanted roots x).length<roots.length := by
  have he : (unwanted roots x).length+multiplicity roots x=roots.length := by
    clear hx
    induction roots with
    | nil => simp [unwanted,multiplicity]
    | cons r rs ih =>
      by_cases h : r=x <;> simp [unwanted,multiplicity,h] at * <;> omega
  have hm := multiplicity_pos roots x hx
  omega

def numerator (roots : List L) (x : L) (moments : ℕ→L) : L :=
  D.differenceFilter (unwanted roots x) moments 0

/-- Zero modes vanish automatically because every queried moment is positive. -/
theorem numerator_eq {A : Type*} [Fintype A] (roots : List L) (c w : A→L)
    (hs : ∀a,w a≠0→w a∈roots) (x : L) :
    numerator roots x (fun k=>∑a,c a*w a^(k+1))=
      (∑a,if w a=x then c a else 0)*denominator roots x := by
  unfold numerator
  rw [D.differenceFilter_moments,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Nat.zero_add,pow_one]
  by_cases he : w a=x
  · simp [he,denominator]
  · rw [ite_eq_right he,zero_mul]
    by_cases hz : w a=0
    · simp [hz]
    · have hm : w a∈unwanted roots x := List.mem_filter.mpr ⟨hs a hz,by simpa using he⟩
      have hp : ((unwanted roots x).map fun r=>w a-r).prod=0 :=
        List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨w a,hm,sub_self _⟩)
      simp [hp]

variable [CharZero L] [StarRing L]

def term (roots : List L) (x : L) (moments : ℕ→L) : L :=
  star x*numerator roots x moments/(denominator roots x*(multiplicity roots x : L))

def result (roots : List L) (moments : ℕ→L) : L :=
  (roots.map fun x=>term roots x moments).sum

theorem term_eq {A : Type*} [Fintype A] (roots : List L) (c w : A→L)
    (hs : ∀a,w a≠0→w a∈roots) (x : L) (hx : x≠0) :
    term roots x (fun k=>∑a,c a*w a^(k+1))=
      ∑a,if w a=x then c a*star x/(multiplicity roots x : L) else 0 := by
  rw [term,numerator_eq roots c w hs,Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : w a=x
  · simp only [ite_eq_left he]
    have hd := denominator_ne_zero roots x hx
    field_simp [hd]
  · simp [he]

private theorem weighted_matches (xs roots : List L) (x z : L) :
    (xs.map fun y=>if x=y then z else 0).sum=(multiplicity xs x : L)*z := by
  induction xs with
  | nil => simp [multiplicity]
  | cons y ys ih =>
    by_cases he : y=x
    · subst y
      simp [multiplicity,ih,add_mul,add_comm]
    · have he' : x≠y := Ne.symm he
      simp [multiplicity,he,he',ih]

theorem result_eq {A : Type*} [Fintype A] (roots : List L) (c w : A→L)
    (hr : ∀r∈roots,r≠0) (hs : ∀a,w a≠0→w a∈roots) :
    result roots (fun k=>∑a,c a*w a^(k+1))=∑a,c a*star (w a) := by
  have ht : (roots.map fun x=>term roots x (fun k=>∑a,c a*w a^(k+1))).sum=
      (roots.map fun x=>∑a,if w a=x then c a*star x/(multiplicity roots x : L) else 0).sum := by
    congr 1
    apply List.map_congr_left
    intro x hx
    exact term_eq roots c w hs x (hr x hx)
  rw [result,ht]
  have commute (rs : List L) :
      (rs.map fun x=>∑a,if w a=x then c a*star x/(multiplicity roots x : L) else 0).sum=
      ∑a,(rs.map fun x=>if w a=x then c a*star x/(multiplicity roots x : L) else 0).sum := by
    induction rs with
    | nil => simp
    | cons x rs ih => simp only [List.map_cons,List.sum_cons,ih,Finset.sum_add_distrib]
  rw [commute]
  apply Finset.sum_congr rfl
  intro a _
  have he : (roots.map fun x=>if w a=x then c a*star x/(multiplicity roots x : L) else 0)=
      roots.map (fun x=>if w a=x then c a*star (w a)/(multiplicity roots (w a) : L) else 0) := by
    apply List.map_congr_left
    intro x _
    by_cases hx : w a=x <;> simp [hx]
  rw [he,weighted_matches roots roots]
  by_cases hz : w a=0
  · simp [hz]
  · have hm : (multiplicity roots (w a) : L)≠0 := by
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (multiplicity_pos roots (w a) (hs a hz)))
    exact mul_div_cancel₀ _ hm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeFilter
