import Holant.Proofs.Hardness.BinaryIsingProgramme
import Holant.Proofs.Hardness.ThreeModeAnnihilatorFilterSemantics
import Holant.Proofs.Hardness.BinaryCSPProgrammeValidated

/-! The concrete interpreter returns the independent-set count, including the
zero-edge graph. Its m positive samples are complemented by the exact zeroth
moment 2^(n+1), and its final multiplication by 1/2 removes the unpinned apex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingProgramme
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot BinaryCSPProgrammeCore
namespace V
export BinaryCSPProgrammeValidated (Input inputEncoding)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
local instance : CharZero K := algebraRat.charZero K
variable (F : FixedField K d) (p q : K)

def moments (r : V.Input) : ℕ→K :=
  BinaryIsingWeights.partition p q (BinaryIsingQuery.left r.val r.property)
    (BinaryIsingQuery.right r.val r.property)

def independentCount (r : V.Input) : K :=
  EOBinaryPlaneIsing.independentCount (BinaryIsingQuery.left r.val r.property)
    (BinaryIsingQuery.right r.val r.property)

omit [Algebra ℚ K] in
@[simp] theorem moments_zero (r : V.Input) : moments p q r 0=total (K:=K) r.val := by
  simp [moments,total]

omit [Algebra ℚ K] in
theorem state_table (r : V.Input) : state p q r.val=
    ((roots p q r.val,
      ThreeModeAnnihilatorFilterSemantics.table ((roots p q r.val).length+1) (moments p q r)),
      (desired p q r.val,1)) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · change total r.val::answers p q r.val=_
      rw [ThreeModeAnnihilatorFilterSemantics.table,List.ofFn_succ]
      congr 1
      · exact (moments_zero p q r).symm
      · apply List.ext_getElem
        · simp [answers,queries,roots]
        · intro i hi hj
          simp only [answers,queries,List.getElem_map,List.getElem_range,List.getElem_ofFn,Fin.val_succ]
          exact BinaryIsingQuery.value_eq_partition p q r.val r.property i
  · rfl

theorem value_formula (r : V.Input) : interpolatedValue F p q r.val=
    (ThreeModeAnnihilator.differenceFilter (roots p q r.val) (moments p q r) 0 /
      BinaryIsingUnnormalized.denominator (desired p q r.val) (q/p) r.val.edges.length)/2 := by
  have hround := (ThreeModeFilter.list_counts_le_bytes F (state p q r.val)).1
  change (roots p q r.val).length≤((S.encoding F).encode (state p q r.val)).length at hround
  unfold interpolatedValue Loop.result ThreeModeFilterLoop.value
  rw [state_table p q r]
  rw [ThreeModeAnnihilatorFilterSemantics.iterate_stable _ _ _ _ _ (by
    simpa only [←state_table p q r] using hround)]
  simp [BinaryIsingUnnormalized.denominator,roots]

theorem independent_correct (hp : p≠0) (hq : q≠0)
    (hr : ∀j,0<j→(q/p)^(2*j)≠1) (r : V.Input) :
    interpolatedValue F p q r.val=independentCount (K:=K) r := by
  rw [value_formula]
  exact (BinaryIsingUnnormalized.extract p q hp hq
    (BinaryIsingQuery.left r.val r.property) (BinaryIsingQuery.right r.val r.property) hr).symm

abbrev ValidQuery := V.Input×ℕ
abbrev validQueryEncoding := pairEncoding V.inputEncoding unary

def validQueryValue (a : ValidQuery) : K := Q.value p q (a.1.val,a.2)

def validQueryOutput : PolynomialOutputBound validQueryEncoding F.encoding (validQueryValue p q) where
  bound := (Q.targetOutput F p q).bound
  length_le a := (Q.targetOutput F p q).length_le (a.1.val,a.2)

theorem valid_execution (oracle : List Bool→List Bool)
    (ho : RepresentsOracle validQueryEncoding F.encoding (validQueryValue p q) oracle) (r : V.Input) :
    ∃t≤(timePolynomial F p q).eval (V.inputEncoding.encode r).length,
      OracleBatch.RunsTrace (machine F p q) oracle ((machine F p q).init (V.inputEncoding.encode r))
        ((machine F p q).output (F.encoding.encode (interpolatedValue F p q r.val))) t
        ((queries r.val).map Q.queryEncoding.encode) := by
  apply execution_agree F p q oracle r.val
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  exact ho (r,i)

def independentControlled (hp : p≠0) (hq : q≠0)
    (hr : ∀j,0<j→(q/p)^(2*j)≠1) :
    LengthControlledOracleReduction V.inputEncoding F.encoding validQueryEncoding F.encoding
      (independentCount (K:=K)) (validQueryValue p q) where
  reduction := {
    machine := machine F p q
    time := timePolynomial F p q
    correct oracle ho r := by
      rw [←independent_correct F p q hp hq hr r]
      let h := valid_execution F p q oracle ho r
      exact {steps:=h.choose,steps_le_m:=h.choose_spec.1,evals_in_steps:=h.choose_spec.2.run} }
  targetOutput := validQueryOutput F p q
  queryBound := (pre F p q).outputBound.bound
  safeQuery oracle ho r t cfg ht hq := by
    obtain ⟨n,_,hrun⟩ := valid_execution F p q oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member hrun t cfg ht hq
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    refine ⟨(r,i),he.symm,?_⟩
    exact (OracleBatch.member_length_le _ _ hm).trans
      (OracleBatch.query_context_length_le (pre F p q) r.val).1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingProgramme
