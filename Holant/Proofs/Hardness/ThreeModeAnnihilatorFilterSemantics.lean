import Holant.Proofs.Hardness.ThreeModeFilter
import Holant.Proofs.Hardness.ThreeModeAnnihilatorEnumeration

/-! The real framed-list difference controller implements the mathematical
annihilator. The theorem identifies its entire final state, and proves that
additional bounded controller rounds leave that state unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilatorFilterSemantics
namespace A
export ThreeModeAnnihilator (differenceFilter mode rootIndices sample denominator)
end A
namespace F
export ThreeModeFilter (State difference step)
end F
variable {K : Type} [Field K]

/-- Exactly the finite prefix of values that the physical controller receives. -/
def table (n : ℕ) (values : ℕ → K) : List K :=
  List.ofFn (fun k : Fin n => values k.val)

omit [Field K] in
@[simp] theorem table_length (n : ℕ) (values : ℕ → K) : (table n values).length=n := by
  simp [table]

/-- One framed-list pass performs one mathematical adjacent difference. -/
theorem difference_table (root : K) (n : ℕ) (values : ℕ → K) :
    F.difference root (table (n+1) values) =
      table n (fun k => values (k+1)-root*values k) := by
  apply List.ext_getElem
  · simp [ThreeModeFilter.difference, table]
  · intro i hi hj
    have hin : i < n := by simpa using hj
    simp only [F.difference, table, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ (by simpa using Nat.succ_lt_succ hin),
      List.getD_eq_getElem _ _ (by simpa using Nat.lt_succ_of_lt hin)]
    simp only [List.getElem_ofFn]

/-- Complete state equality after exactly the number of root factors. -/
theorem iterate_exact (roots : List K) (values : ℕ → K) (desired den : K) :
    F.step^[roots.length] ((roots,table (roots.length+1) values),(desired,den)) =
      (([],[A.differenceFilter roots values 0]),
        (desired,den*(roots.map (fun r => desired-r)).prod)) := by
  induction roots generalizing values den with
  | nil => simp [table, List.ofFn_succ]
  | cons r rs ih =>
      simp only [List.length_cons, Function.iterate_succ_apply]
      have hs : F.step ((r::rs,table (rs.length+1+1) values),(desired,den)) =
          ((rs,F.difference r (table (rs.length+1+1) values)),(desired,den*(desired-r))) := by
        simp [F.step]
      rw [hs, difference_table, ih]
      simp only [ThreeModeAnnihilator.differenceFilter_cons, List.map_cons, List.prod_cons,
        mul_assoc]

/-- Extra rounds are safe: an empty remaining-root list is a genuine fixed point. -/
theorem iterate_stable (roots : List K) (values : ℕ → K) (desired den : K)
    (rounds : ℕ) (hrounds : roots.length ≤ rounds) :
    F.step^[rounds] ((roots,table (roots.length+1) values),(desired,den)) =
      (([],[A.differenceFilter roots values 0]),
        (desired,den*(roots.map (fun r => desired-r)).prod)) := by
  have hr : rounds=(rounds-roots.length)+roots.length := by omega
  rw [hr, Function.iterate_add_apply, iterate_exact]
  apply Function.iterate_fixed
  simp [F.step]

/-- The exact statement in terms of the caller's finite `List.ofFn` answers. -/
theorem iterate_ofFn (roots : List K) (values : ℕ → K) (desired den : K) :
    F.step^[roots.length]
      ((roots,List.ofFn (fun k : Fin (roots.length+1) => values k.val)),(desired,den)) =
      (([],[A.differenceFilter roots values 0]),
        (desired,den*(roots.map (fun r => desired-r)).prod)) :=
  iterate_exact roots values desired den

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeAnnihilatorFilterSemantics
